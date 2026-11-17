#include "7-rule-summary.h"
#include <inttypes.h>
#include <string.h>

// STEP 7 - RULE SUMMARY
//
// The summary is computed by walking the parse tree of the grammar (which
// keeps the structural expressions: sequences, choices, repetitions, and so
// on) together with the rule table built in step 2 (which gives the rule
// order, the token rules and the named-choice/operator layout).
//
// A "length" counts tokens consumed: every literal or token rule matches one
// token, sequences add lengths, choices take the minimum or maximum over
// their branches, and repetitions scale their operand's length by their
// bounds.  Lengths are computed to a fixed point, so recursive grammars get
// finite minimum lengths while any rule on a cycle gets an infinite maximum.

// A length interval.  `infinite` means the value is unbounded; in that case
// `value` holds the best finite bound found so far (UINT64_MAX when none).
struct length {
    uint64_t value;
    bool infinite;
};

#define LENGTH_ZERO ((struct length){ .value = 0, .infinite = false })
#define LENGTH_INFINITY ((struct length){ .value = UINT64_MAX, \
 .infinite = true })

struct rule_summary {
    // The parse-tree rule node, or an empty ref for token rules that were
    // generated while building the grammar (identifier, integer, ...).
    struct owl_ref parsed_rule;

    struct length minimum;
    struct length maximum;
    bool nullable;

    // Bookkeeping for the maximum-length depth-first search: white (0) is
    // unvisited, gray (1) is on the active search stack, black (2) is done.
    unsigned char *max_color;

    // Bookkeeping for the reachability search.
    bool reachable;
};

struct summary_context {
    const struct grammar *grammar;
    struct owl_tree *tree;
    struct rule_summary *rules;
    unsigned char *max_color;
};

static struct length length_saturating_add(struct length a, struct length b);
static struct length length_min(struct length a, struct length b);
static struct length length_max(struct length a, struct length b);
static struct length length_scale(struct length l, uint64_t factor);
static uint32_t find_rule_index(const struct grammar *grammar,
 const char *name, size_t name_length);
static struct length rule_minimum(struct summary_context *ctx, uint32_t index);
static struct length rule_maximum(struct summary_context *ctx, uint32_t index);
static struct length expression_minimum(struct summary_context *ctx,
 struct owl_ref expr_ref);
static struct length expression_maximum(struct summary_context *ctx,
 struct owl_ref expr_ref);
static bool rule_nullable(struct summary_context *ctx, uint32_t index);
static bool expression_nullable(struct summary_context *ctx,
 struct owl_ref expr_ref);
static void repetition_bounds(struct parsed_expr expr, uint64_t *min_count,
 uint64_t *max_count, bool *unbounded);
static void mark_expression_reachable(struct summary_context *ctx,
 struct owl_ref expr_ref);
static void mark_rule_reachable(struct summary_context *ctx, uint32_t index);

void print_rule_summary(FILE *file, const struct grammar *grammar,
 const struct owl_tree *tree)
{
    // The parse-tree accessors take a non-const tree pointer even though
    // they only read from it.
    struct summary_context ctx = {
        .grammar = grammar,
        .tree = (struct owl_tree *)tree,
    };
    ctx.rules = calloc(grammar->number_of_rules, sizeof(*ctx.rules));
    if (grammar->number_of_rules > 0 && !ctx.rules)
        abort();
    ctx.max_color = calloc(grammar->number_of_rules, sizeof(*ctx.max_color));
    if (grammar->number_of_rules > 0 && !ctx.max_color)
        abort();
    for (uint32_t i = 0; i < grammar->number_of_rules; ++i)
        ctx.rules[i].minimum = LENGTH_INFINITY;
    for (uint32_t i = 0; i < grammar->number_of_rules; ++i)
        ctx.rules[i].maximum = LENGTH_INFINITY;

    // Match each parsed rule with its entry in the rule table.  The table is
    // built by walking the same parse-tree list, so the name lookup just
    // guards against the generated token rules.
    struct parsed_grammar parsed = owl_tree_get_parsed_grammar(ctx.tree);
    for (struct owl_ref r = parsed.rule; !r.empty; r = owl_next(r)) {
        struct parsed_rule parsed_rule = parsed_rule_get(r);
        struct parsed_identifier name =
         parsed_identifier_get(parsed_rule.identifier);
        uint32_t index = find_rule_index(grammar, name.identifier,
         name.length);
        if (index == UINT32_MAX)
            abort();
        ctx.rules[index].parsed_rule = r;
    }

    // Minimum lengths and nullability are least fixed points over the rule
    // table: start with "infinite / not nullable" and relax until no value
    // changes.  Recursive references therefore converge to a finite minimum
    // instead of poisoning the whole computation.
    bool changed = true;
    while (changed) {
        changed = false;
        for (uint32_t i = 0; i < grammar->number_of_rules; ++i) {
            struct length min = rule_minimum(&ctx, i);
            bool nullable = rule_nullable(&ctx, i);
            if (min.infinite != ctx.rules[i].minimum.infinite ||
             (!min.infinite && min.value != ctx.rules[i].minimum.value)) {
                ctx.rules[i].minimum = min;
                changed = true;
            }
            if (nullable != ctx.rules[i].nullable) {
                ctx.rules[i].nullable = nullable;
                changed = true;
            }
        }
    }

    // Maximum lengths are found with a depth-first search over rule
    // references: a back edge means an unbounded cycle, so the rule's
    // maximum is infinity.  Finite results are memoized; the fixed point
    // above already guarantees every minimum converges.
    for (uint32_t i = 0; i < grammar->number_of_rules; ++i)
        (void)rule_maximum(&ctx, i);

    // Reachability: walk rule references starting from the root rule.
    // Anything the walk doesn't touch can never participate in a match.
    mark_rule_reachable(&ctx, grammar->root_rule);

    // Print one line per rule, in rule-table order, which is the order in
    // which the rules appear in the grammar (with generated token rules
    // inserted at the point of their first use).
    for (uint32_t i = 0; i < grammar->number_of_rules; ++i) {
        const struct rule *rule = grammar->rules[i];
        fprintf(file, "%.*s min=", (int)rule->name_length, rule->name);
        if (ctx.rules[i].minimum.infinite)
            fputs("infinity", file);
        else
            fprintf(file, "%" PRIu64, ctx.rules[i].minimum.value);
        fputs(" max=", file);
        if (ctx.rules[i].maximum.infinite)
            fputs("infinity", file);
        else
            fprintf(file, "%" PRIu64, ctx.rules[i].maximum.value);
        fprintf(file, " nullable=%s\n", ctx.rules[i].nullable ? "yes" : "no");
    }

    // The reachability list is filled in a later increment.
    fputs("unreachable:", file);
    bool first = true;
    for (uint32_t i = 0; i < grammar->number_of_rules; ++i) {
        if (ctx.rules[i].reachable)
            continue;
        fputs(first ? " " : ", ", file);
        first = false;
        const struct rule *rule = grammar->rules[i];
        fprintf(file, "%.*s", (int)rule->name_length, rule->name);
    }
    fputc('\n', file);

    free(ctx.max_color);
    free(ctx.rules);
}

static uint32_t find_rule_index(const struct grammar *grammar,
 const char *name, size_t name_length)
{
    for (uint32_t i = 0; i < grammar->number_of_rules; ++i) {
        const struct rule *rule = grammar->rules[i];
        if (rule->name_length == name_length &&
         !memcmp(rule->name, name, name_length))
            return i;
    }
    return UINT32_MAX;
}

static struct length length_saturating_add(struct length a, struct length b)
{
    if (a.infinite || b.infinite)
        return LENGTH_INFINITY;
    if (a.value > UINT64_MAX - b.value)
        return LENGTH_INFINITY;
    return (struct length){
        .value = a.value + b.value,
        .infinite = false,
    };
}

static struct length length_min(struct length a, struct length b)
{
    if (a.infinite)
        return b;
    if (b.infinite)
        return a;
    return (struct length){
        .value = a.value < b.value ? a.value : b.value,
        .infinite = false,
    };
}

static struct length length_max(struct length a, struct length b)
{
    if (a.infinite || b.infinite)
        return LENGTH_INFINITY;
    return (struct length){
        .value = a.value > b.value ? a.value : b.value,
        .infinite = false,
    };
}

static struct length length_scale(struct length l, uint64_t factor)
{
    if (factor == 0)
        return LENGTH_ZERO;
    if (l.infinite)
        return LENGTH_INFINITY;
    // Saturate: repeated doubling can't overshoot by more than a factor of
    // two, and any overflow means the finite bound exceeds uint64_t.
    uint64_t result = 0;
    uint64_t addend = l.value;
    uint64_t remaining = factor;
    while (remaining > 0) {
        if (remaining & 1) {
            if (addend > UINT64_MAX - result)
                return LENGTH_INFINITY;
            result += addend;
        }
        remaining >>= 1;
        if (remaining > 0) {
            if (addend > UINT64_MAX / 2)
                return LENGTH_INFINITY;
            addend *= 2;
        }
    }
    return (struct length){ .value = result, .infinite = false };
}

// Token rules (the built-in identifier/integer/number/string classes and
// user-defined .token rules) always match a single token.
static struct length rule_minimum(struct summary_context *ctx, uint32_t index)
{
    const struct rule *rule = ctx->grammar->rules[index];
    if (rule->is_token)
        return (struct length){ .value = 1, .infinite = false };
    struct rule_summary *summary = &ctx->rules[index];
    if (summary->parsed_rule.empty)
        abort();
    struct parsed_rule parsed_rule = parsed_rule_get(summary->parsed_rule);
    struct parsed_body body = parsed_body_get(parsed_rule.body);

    // Simple rule: one expression.
    if (body.identifier.empty)
        return expression_minimum(ctx, body.expr);

    // Rule with named choices.  The base choices can be picked directly...
    struct length result = LENGTH_INFINITY;
    for (struct owl_ref e = body.expr; !e.empty; e = owl_next(e))
        result = length_min(result, expression_minimum(ctx, e));

    // ...and each operator group wraps the level below it.  Prefix and
    // postfix groups repeat zero or more times, so the minimum is unchanged;
    // a non-associative infix group requires a second operand when used.
    for (struct owl_ref o = body.operators; !o.empty; o = owl_next(o)) {
        struct parsed_operators ops = parsed_operators_get(o);
        struct parsed_fixity fixity = parsed_fixity_get(ops.fixity);
        if (fixity.type == PARSED_NONASSOC_OP ||
         (fixity.type == PARSED_INFIX_OP && !fixity.assoc.empty &&
         parsed_assoc_get(fixity.assoc).type == PARSED_NONASSOC_OP)) {
            struct length smallest_operator = LENGTH_INFINITY;
            for (struct owl_ref p = ops.operator; !p.empty;
             p = owl_next(p)) {
                struct parsed_operator op = parsed_operator_get(p);
                smallest_operator = length_min(smallest_operator,
                 expression_minimum(ctx, op.expr));
            }
            // Either one operand, or two operands joined by an operator.
            struct length with_operator = length_saturating_add(
             length_saturating_add(result, smallest_operator), result);
            result = length_min(result, with_operator);
        }
        // Prefix, postfix and the other infix groups add nothing to the
        // minimum: zero repetitions still match the underlying level.
    }
    return result;
}

static struct length expression_minimum(struct summary_context *ctx,
 struct owl_ref expr_ref)
{
    struct parsed_expr expr = parsed_expr_get(expr_ref);
    switch (expr.type) {
    case PARSED_LITERAL:
        // An empty keyword '' matches the empty token sequence.
        return parsed_string_get(expr.string).length == 0 ? LENGTH_ZERO :
         (struct length){ .value = 1, .infinite = false };
    case PARSED_IDENT: {
        struct parsed_identifier ident =
         parsed_identifier_get(expr.identifier);
        uint32_t index = find_rule_index(ctx->grammar, ident.identifier,
         ident.length);
        if (index == UINT32_MAX)
            abort();
        // Read the current best value so the fixed point can relax.
        return ctx->rules[index].minimum;
    }
    case PARSED_PARENS:
        return expression_minimum(ctx, expr.expr);
    case PARSED_BRACKETED: {
        // Begin keyword, contents, end keyword: two fixed tokens around the
        // inner expression (empty brackets are rejected when building).
        struct length inner = expr.expr.empty ? LENGTH_ZERO :
         expression_minimum(ctx, expr.expr);
        return length_saturating_add(
         (struct length){ .value = 2, .infinite = false }, inner);
    }
    case PARSED_CHOICE: {
        struct length result = LENGTH_INFINITY;
        for (struct owl_ref o = expr.operand; !o.empty; o = owl_next(o))
            result = length_min(result, expression_minimum(ctx, o));
        return result;
    }
    case PARSED_CONCATENATION: {
        struct length result = LENGTH_ZERO;
        for (struct owl_ref o = expr.operand; !o.empty; o = owl_next(o))
            result = length_saturating_add(result,
             expression_minimum(ctx, o));
        return result;
    }
    case PARSED_OPTIONAL:
        return LENGTH_ZERO;
    case PARSED_ZERO_OR_MORE:
        return LENGTH_ZERO;
    case PARSED_ONE_OR_MORE:
        return expression_minimum(ctx, expr.operand);
    case PARSED_REPETITION: {
        uint64_t min_count, max_count;
        bool unbounded;
        repetition_bounds(expr, &min_count, &max_count, &unbounded);
        struct length operand = expression_minimum(ctx, expr.operand);
        if (expr.expr.empty)
            return length_scale(operand, min_count);
        // With a delimiter: n operands and n-1 delimiters.
        struct length delimiter = expression_minimum(ctx, expr.expr);
        if (min_count == 0)
            return LENGTH_ZERO;
        return length_saturating_add(length_scale(operand, min_count),
         length_scale(delimiter, min_count - 1));
    }
    default:
        // PARSED_RANGE only occurs inside repetition counts.
        abort();
    }
}

// Depth-first search for a rule's maximum length.  Re-entering an active
// Depth-first search for a rule's maximum length.  Re-entering a gray rule
// closes a cycle, which can repeat forever and therefore makes the maximum
// infinite: the back edge returns infinity, and every rule unwinding below
// that point inherits it through the ordinary length arithmetic.  Black
// rules use their memoized value.
static struct length rule_maximum(struct summary_context *ctx, uint32_t index)
{
    enum { WHITE, GRAY, BLACK };
    if (ctx->max_color[index] == BLACK)
        return ctx->rules[index].maximum;
    if (ctx->max_color[index] == GRAY)
        return LENGTH_INFINITY;
    const struct rule *rule = ctx->grammar->rules[index];
    if (rule->is_token) {
        ctx->max_color[index] = BLACK;
        ctx->rules[index].maximum =
         (struct length){ .value = 1, .infinite = false };
        return ctx->rules[index].maximum;
    }
    if (ctx->rules[index].parsed_rule.empty)
        abort();
    ctx->max_color[index] = GRAY;
    struct parsed_rule parsed_rule =
     parsed_rule_get(ctx->rules[index].parsed_rule);
    struct parsed_body body = parsed_body_get(parsed_rule.body);

    struct length result;
    if (body.identifier.empty) {
        // Simple rule: one expression.
        result = expression_maximum(ctx, body.expr);
    } else {
        // Named choices: take the largest branch.
        result = LENGTH_ZERO;
        for (struct owl_ref e = body.expr; !e.empty; e = owl_next(e))
            result = length_max(result, expression_maximum(ctx, e));

        // Each operator group wraps the level below it.  Prefix, postfix
        // and ordinary infix groups repeat, so they make the maximum
        // infinite as soon as any operator exists; a non-associative
        // infix group can be used at most once, so it stays finite.
        for (struct owl_ref o = body.operators; !o.empty;
         o = owl_next(o)) {
            struct parsed_operators ops = parsed_operators_get(o);
            struct parsed_fixity fixity = parsed_fixity_get(ops.fixity);
            bool nonassoc = fixity.type == PARSED_NONASSOC_OP ||
             (fixity.type == PARSED_INFIX_OP && !fixity.assoc.empty &&
             parsed_assoc_get(fixity.assoc).type == PARSED_NONASSOC_OP);
            if (!nonassoc) {
                result = LENGTH_INFINITY;
            } else {
                struct length largest_operator = LENGTH_ZERO;
                for (struct owl_ref p = ops.operator; !p.empty;
                 p = owl_next(p)) {
                    struct parsed_operator op = parsed_operator_get(p);
                    largest_operator = length_max(largest_operator,
                     expression_maximum(ctx, op.expr));
                }
                // One operand, or two operands joined by an operator.
                struct length with_operator = length_saturating_add(
                 length_saturating_add(result, largest_operator), result);
                result = length_max(result, with_operator);
            }
        }
    }

    ctx->max_color[index] = BLACK;
    ctx->rules[index].maximum = result;
    return result;
}

static struct length expression_maximum(struct summary_context *ctx,
 struct owl_ref expr_ref)
{
    struct parsed_expr expr = parsed_expr_get(expr_ref);
    switch (expr.type) {
    case PARSED_LITERAL:
        return parsed_string_get(expr.string).length == 0 ? LENGTH_ZERO :
         (struct length){ .value = 1, .infinite = false };
    case PARSED_IDENT: {
        struct parsed_identifier ident =
         parsed_identifier_get(expr.identifier);
        uint32_t index = find_rule_index(ctx->grammar, ident.identifier,
         ident.length);
        if (index == UINT32_MAX)
            abort();
        return rule_maximum(ctx, index);
    }
    case PARSED_PARENS:
        return expression_maximum(ctx, expr.expr);
    case PARSED_BRACKETED: {
        struct length inner = expr.expr.empty ? LENGTH_ZERO :
         expression_maximum(ctx, expr.expr);
        return length_saturating_add(
         (struct length){ .value = 2, .infinite = false }, inner);
    }
    case PARSED_CHOICE: {
        struct length result = LENGTH_ZERO;
        for (struct owl_ref o = expr.operand; !o.empty; o = owl_next(o))
            result = length_max(result, expression_maximum(ctx, o));
        return result;
    }
    case PARSED_CONCATENATION: {
        struct length result = LENGTH_ZERO;
        for (struct owl_ref o = expr.operand; !o.empty; o = owl_next(o))
            result = length_saturating_add(result,
             expression_maximum(ctx, o));
        return result;
    }
    case PARSED_OPTIONAL:
        return expression_maximum(ctx, expr.operand);
    case PARSED_ZERO_OR_MORE:
    case PARSED_ONE_OR_MORE:
        return LENGTH_INFINITY;
    case PARSED_REPETITION: {
        uint64_t min_count, max_count;
        bool unbounded;
        repetition_bounds(expr, &min_count, &max_count, &unbounded);
        struct length operand = expression_maximum(ctx, expr.operand);
        if (expr.expr.empty) {
            if (unbounded)
                return LENGTH_INFINITY;
            return length_scale(operand, max_count);
        }
        // With a delimiter: n operands and n-1 delimiters.
        struct length delimiter = expression_maximum(ctx, expr.expr);
        if (unbounded)
            return LENGTH_INFINITY;
        if (max_count == 0)
            return LENGTH_ZERO;
        return length_saturating_add(length_scale(operand, max_count),
         length_scale(delimiter, max_count - 1));
    }
    default:
        abort();
    }
}

static bool rule_nullable(struct summary_context *ctx, uint32_t index)
{
    const struct rule *rule = ctx->grammar->rules[index];
    if (rule->is_token)
        return false;
    struct rule_summary *summary = &ctx->rules[index];
    if (summary->parsed_rule.empty)
        abort();
    struct parsed_rule parsed_rule = parsed_rule_get(summary->parsed_rule);
    struct parsed_body body = parsed_body_get(parsed_rule.body);

    if (body.identifier.empty)
        return expression_nullable(ctx, body.expr);

    // A choice rule is nullable if any base choice is nullable.  Prefix,
    // postfix and ordinary infix operator groups all allow zero operator
    // occurrences, so they don't change nullability; a non-associative
    // infix group likewise still permits skipping the operator entirely.
    for (struct owl_ref e = body.expr; !e.empty; e = owl_next(e)) {
        if (expression_nullable(ctx, e))
            return true;
    }
    return false;
}

static bool expression_nullable(struct summary_context *ctx,
 struct owl_ref expr_ref)
{
    struct parsed_expr expr = parsed_expr_get(expr_ref);
    switch (expr.type) {
    case PARSED_LITERAL:
        return parsed_string_get(expr.string).length == 0;
    case PARSED_IDENT: {
        struct parsed_identifier ident =
         parsed_identifier_get(expr.identifier);
        uint32_t index = find_rule_index(ctx->grammar, ident.identifier,
         ident.length);
        if (index == UINT32_MAX)
            abort();
        return ctx->rules[index].nullable;
    }
    case PARSED_PARENS:
        return expression_nullable(ctx, expr.expr);
    case PARSED_BRACKETED:
        // Guard brackets always consume their begin and end keywords.
        return false;
    case PARSED_CHOICE:
        for (struct owl_ref o = expr.operand; !o.empty; o = owl_next(o)) {
            if (expression_nullable(ctx, o))
                return true;
        }
        return false;
    case PARSED_CONCATENATION:
        for (struct owl_ref o = expr.operand; !o.empty; o = owl_next(o)) {
            if (!expression_nullable(ctx, o))
                return false;
        }
        return true;
    case PARSED_OPTIONAL:
    case PARSED_ZERO_OR_MORE:
        return true;
    case PARSED_ONE_OR_MORE:
        return expression_nullable(ctx, expr.operand);
    case PARSED_REPETITION: {
        uint64_t min_count, max_count;
        bool unbounded;
        repetition_bounds(expr, &min_count, &max_count, &unbounded);
        if (min_count > 0)
            return false;
        if (expr.expr.empty)
            return true;
        // A zero-count branch exists, so a delimiter never has to match.
        return true;
    }
    default:
        abort();
    }
}

// Extract the repetition counts from a PARSED_REPETITION node.  No
// repetition clause means "any number", i.e. {0+}.
static void repetition_bounds(struct parsed_expr expr, uint64_t *min_count,
 uint64_t *max_count, bool *unbounded)
{
    if (expr.repetition.empty) {
        *min_count = 0;
        *max_count = 0;
        *unbounded = true;
        return;
    }
    struct parsed_repetition repetition =
     parsed_repetition_get(expr.repetition);
    uint64_t begin = parsed_integer_get(repetition.begin).integer;
    switch (repetition.type) {
    case PARSED_EXACT:
        *min_count = *max_count = begin;
        *unbounded = false;
        break;
    case PARSED_RANGE:
        *min_count = begin;
        *max_count = parsed_integer_get(repetition.end).integer;
        *unbounded = false;
        break;
    case PARSED_AT_LEAST:
        *min_count = begin;
        *max_count = 0;
        *unbounded = true;
        break;
    default:
        abort();
    }
}

static void mark_rule_reachable(struct summary_context *ctx, uint32_t index)
{
    if (ctx->rules[index].reachable)
        return;
    ctx->rules[index].reachable = true;
    const struct rule *rule = ctx->grammar->rules[index];
    if (rule->is_token)
        return;
    if (ctx->rules[index].parsed_rule.empty)
        abort();
    struct parsed_rule parsed_rule =
     parsed_rule_get(ctx->rules[index].parsed_rule);
    struct parsed_body body = parsed_body_get(parsed_rule.body);
    if (body.identifier.empty) {
        mark_expression_reachable(ctx, body.expr);
        return;
    }
    for (struct owl_ref e = body.expr; !e.empty; e = owl_next(e))
        mark_expression_reachable(ctx, e);
    for (struct owl_ref o = body.operators; !o.empty;
     o = owl_next(o)) {
        struct parsed_operators ops = parsed_operators_get(o);
        for (struct owl_ref p = ops.operator; !p.empty;
         p = owl_next(p)) {
            struct parsed_operator op = parsed_operator_get(p);
            mark_expression_reachable(ctx, op.expr);
        }
    }
}

static void mark_expression_reachable(struct summary_context *ctx,
 struct owl_ref expr_ref)
{
    struct parsed_expr expr = parsed_expr_get(expr_ref);
    switch (expr.type) {
    case PARSED_LITERAL:
        break;
    case PARSED_IDENT: {
        struct parsed_identifier ident =
         parsed_identifier_get(expr.identifier);
        uint32_t index = find_rule_index(ctx->grammar, ident.identifier,
         ident.length);
        if (index == UINT32_MAX)
            abort();
        mark_rule_reachable(ctx, index);
        break;
    }
    case PARSED_PARENS:
        mark_expression_reachable(ctx, expr.expr);
        break;
    case PARSED_BRACKETED:
        if (!expr.expr.empty)
            mark_expression_reachable(ctx, expr.expr);
        break;
    case PARSED_CHOICE:
    case PARSED_CONCATENATION:
        for (struct owl_ref o = expr.operand; !o.empty; o = owl_next(o))
            mark_expression_reachable(ctx, o);
        break;
    case PARSED_OPTIONAL:
    case PARSED_ZERO_OR_MORE:
    case PARSED_ONE_OR_MORE:
        mark_expression_reachable(ctx, expr.operand);
        break;
    case PARSED_REPETITION:
        mark_expression_reachable(ctx, expr.operand);
        if (!expr.expr.empty)
            mark_expression_reachable(ctx, expr.expr);
        break;
    default:
        abort();
    }
}
