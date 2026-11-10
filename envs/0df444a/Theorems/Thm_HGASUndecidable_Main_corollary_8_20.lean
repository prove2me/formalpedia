-- Prove2me | Theorems.Thm_HGASUndecidable_Main_corollary_8_20
-- name    : HGASUndecidable.Main.corollary_8_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:17:31.44641+00:00
-- url     : https://prove2.me/theorems/e05b6f32-546f-49e3-83b2-f68d07a11cdc
-- title:
--   Corollary 8.20 — e ∈ K iff no solution of ẋ = Xe(x) satisfying (ii), (iv) passes the tests
-- statement:
--   Use the full system and test map of Section 8.4.1. Passing the tests means that every test coordinate has an existing zero time average and every validity residual vanishes at every real time. Moderate growth means the bound for some real exponent μ ≥ 1, and recurrence is along a sequence of positive times tending to infinity. Corollary 8.20. Let e ∈ N. Then e ∈ K if and only if there is no solution x : R → R^{ns} of ẋ = Xe(x) which satisfies (ii) and (iv) of Theorem 8.18 and passes the tests.
--
--   Differences from the source:
--   - encoding: Euclidean spaces with coordinates numbered from one → State n = EuclideanSpace ℝ (Fin n), with coordinates numbered from zero; reason: the coordinate identification preserves the Euclidean norm and every instance
--   - encoding: the halting set of a universal Turing machine on paired input → definedness of (Nat.Partrec.Code.ofNatCode e.unpair.1).eval e.unpair.2; reason: this is the universal partial-recursive halting problem, with the same many-one completeness convention
--   - generalization: the fixed data q,r,A,B,c₀,c₁ chosen after Lemma 7.2 → every DiophantineData satisfying positivity, nonzero columns of B, and the halting-solvability equivalence; reason: the subsequent construction and assertions use exactly these properties and specialize to the fixed source choice
--   - encoding: real and complex blocks on ℝⁿˢ with nₛ = 38q+4r+2 → one Euclidean vector, ordered as four real coordinates per clock, two oscillator coordinates, and 34 real coordinates per variable; reason: complex polynomials are split coefficientwise into real and imaginary parts; the coordinate permutation changes no equations or norm
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Corollary 8.20, printed p. 59 (PDF 61)

import Definitions.Def_HGASUndecidable_Main_System

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem corollary_8_20 (a : DiophantineData) (ha : DiophantineValid a) (e : ℕ) :
    haltingSet e ↔ ¬∃ x : ℝ → State (ns a), EntireSolution (system a e) x ∧
      forwardRecurrent x ∧ moderateGrowth x ∧ PassesTests a x := by sorry

end HGASUndecidable.Main
