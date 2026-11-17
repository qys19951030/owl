#ifndef RULE_SUMMARY_H
#define RULE_SUMMARY_H

#include "1-parse.h"
#include "2-build.h"
#include <stdio.h>

// STEP 7 - RULE SUMMARY
//
// This step walks the parsed grammar and the rule table built in step 2 to
// print a structural summary of the grammar to the given file (normally
// standard error).  The summary lists, for every rule, the minimum and
// maximum number of characters (tokens) a match can consume and whether the
// rule is nullable, followed by the list of rules that can't be reached from
// the root rule.  It doesn't modify the grammar or the parse tree, so the
// rest of the pipeline produces byte-identical output whether or not a
// summary is requested.

// Print the rule summary for `grammar` (whose parse tree is `tree`) to
// `file`.  The grammar must have been built already; the parse tree is used
// to read the structural expressions of the rules.
void print_rule_summary(FILE *file, const struct grammar *grammar,
 const struct owl_tree *tree);

#endif
