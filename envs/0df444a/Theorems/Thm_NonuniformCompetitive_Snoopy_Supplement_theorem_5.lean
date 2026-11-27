-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_5
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:02:28.23234+00:00
-- url     : https://prove2.me/theorems/f87c052d-d978-43c9-9acf-cd1867e82d29
-- title:
--   Theorem 5 — adaptive online caching lower bound 2
-- statement:
--   Fix $n\ge2$ processors, integral transfer cost $p\ge1$, and any initial cache state $s_0$. Let $A$ be any randomized causal caching algorithm whose observed states are measurable. If one constant makes $A$ competitive against every bounded causal input strategy and every causal online comparison algorithm on the same generated requests, then
--   $$c\ge2.$$
--   The comparison includes the source's additive constant and arbitrary finite request bounds. A single cache block already witnesses the lower bound, so an algorithm for the whole problem cannot evade it by handling more blocks.
--
--   This distinguishes adaptive online comparison from the oblivious and adaptive offline models.
--
--   Differences from the source:
--   - encoding: a snoopy-caching system in the nontrivial source setting → n ≥ 2 processors and p ≥ 1, with arbitrary initial state; reason: one processor has no cross-cache lower bound and transfer cost is a positive integer
--   - reading: random costs in an adaptive interaction → measurable observed states, measurable interacting costs and finite-cost online comparators; reason: fixed-word cost measurability alone does not license an adaptive expectation; infeasible infinite comparators are irrelevant
--   - encoding: request length bounded by f(S) regardless of random choices → arbitrary strategies truncated at arbitrary N before quantifying the one additive constant; reason: every bounded causal request generator is represented
--   - encoding: no algorithm for snoopy caching beats 2 → the lower bound already on one block, as in the source proof; reason: restriction of any full-system algorithm to requests for one block is a causal algorithm of this type
--   - generalization: the adaptive on-line adversary serves with knowledge of A's past actions → the comparator B is a fixed causal algorithm of the generated request prefix only, and tests are restricted to measurable bounded interactions; reason: the hypothesis covers fewer adversaries, so the lower bound is stronger; the source adversary (shared or private per phase from A's expected write count) is of this form because the request prefix reveals when A went private
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 554, Theorem 5 and governing context

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_adaptiveSnoopy

namespace NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 5, p.554: adaptive online lower bound, already witnessed by one
block. At least two processors and positive integral transfer cost are the
nondegenerate source setting. Randomized policies are arbitrary causal policies,
not only phase or threshold policies. The same a must cover arbitrarily many
bounded interactions. Observed actions must be measurable, as required for the
source's adaptive random experiment. -/
theorem theorem_5 (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p)
    (s₀ : NonuniformCompetitive.Snoopy.State n)
    (A : NonuniformCompetitive.Snoopy.RandomizedAlgorithm n p) (hreg : SnoopyRegular A)
    (c : ℝ) (hA : SnoopyAdaptiveCompetitive A s₀ c) : 2 ≤ c := by sorry

end NonuniformCompetitive.Snoopy.Supplement
