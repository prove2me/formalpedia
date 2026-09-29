-- Prove2me | Theorems.Thm_LeanEval_NumberTheory_riemann_hypothesis_iff_lagarias_elementary_criterion
-- name    : LeanEval.NumberTheory.riemann_hypothesis_iff_lagarias_elementary_criterion
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-06T02:08:56.974393+00:00
-- url     : https://prove2.me/theorems/86ef0a90-5cda-409b-b56d-fe87fcb29d31
-- title:
--   Lagarias criterion is equivalent to RH
-- statement:
--   The Riemann hypothesis is equivalent to the assertion that, for every positive integer $n$,
--
--   $$\sigma(n)\le H_n+\exp(H_n)\log(H_n),$$
--
--   where $\sigma(n)=\sum_{d\mid n}d$ and $H_n=\sum_{j=1}^n1/j$. This is the exact LeanEval v1 target: both directions of the equivalence, with no hypotheses, no finite cutoff, and no equality-only clause. It asks for formalization of a known equivalence, not a proof that RH or the universal arithmetic criterion holds.
--
--   **Source distinction.** Lagarias's Problem E also specifies equality only at $n=1$. The goal deliberately uses the weaker non-strict criterion required by the benchmark; the reverse argument on p. 8 needs only this inequality.
-- source:
--   Jeffrey C. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis, arXiv:math/0008177v2 (6 May 2001), https://arxiv.org/abs/math/0008177v2, p. 1, Theorem 1.1 and Problem E, equation (1.1); p. 8, proof using only the non-strict inequality for the reverse implication. Exact goal: LeanEval/NumberTheory/Lagarias.lean, statement revision 1.

import Definitions.Def_LeanEval_NumberTheory_LagariasElementaryCriterion

namespace LeanEval.NumberTheory

theorem riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis ↔ LagariasElementaryCriterion := by sorry

end LeanEval.NumberTheory
