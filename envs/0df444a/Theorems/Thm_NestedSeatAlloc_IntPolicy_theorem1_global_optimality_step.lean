-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_global_optimality_step
-- name    : NestedSeatAlloc.IntPolicy.theorem1_global_optimality_step
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-06T07:16:39.681563+00:00
-- url     : https://prove2.me/theorems/1a225ec4-79f4-441b-8cab-36ea4a79c8fb
-- title:
--   Theorem 1 optimality step — extend policy dominance by one fare class
-- statement:
--   If a policy dominates every protection policy through nest k and satisfies the subdifferential condition at k, then it dominates every protection policy through nest k+1.
-- source:
--   Source-faithful one-step decomposition of Brumelle & McGill (1993), Theorem 1 optimality induction, pp. 131–132.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_global_optimality_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ) (s : ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (hk : 1 ≤ k) (hs : 0 ≤ s)
    (h20k : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (hprev : ∀ q, IsProtectionPolicy q →
      expRevenue P X f q k s ≤ expRevenue P X f p k s) :
    ∀ q, IsProtectionPolicy q →
      expRevenue P X f q (k + 1) s ≤ expRevenue P X f p (k + 1) s := by sorry

end NestedSeatAlloc.IntPolicy
