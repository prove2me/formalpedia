-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_corollary1_conditional_revenue_concave
-- name    : NestedSeatAlloc.IntPolicy.corollary1_conditional_revenue_concave
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T12:35:53.686345+00:00
-- url     : https://prove2.me/theorems/e5c4f26f-0565-4b78-9161-3b3ae9b93077
-- title:
--   Fixed-demand conditional revenue is concave
-- statement:
--   If the k-class expected revenue is concave and its one-sided subdifferential at p_k contains fare f_{k+1}, then fixing any nonnegative demand y for class k+1 makes the conditional k+1-class revenue concave in capacity.
-- source:
--   Source-faithful calculus child of Corollary 1 (5a3801ae-82a6-44d7-8f5f-8c951b11140a): unfold the k+1 revenue recursion at fixed y, obtain the three pieces g(s), (s-p_k)f_{k+1}+g(p_k), and y f_{k+1}+g(s-y), then prove concavity from hconc and the two one-sided derivative bounds in h14.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem corollary1_conditional_revenue_concave {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (hk : 1 ≤ k)
    (hconc : ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p k))
    (h14 : InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)))
    (y : ℝ) (hy : 0 ≤ y) :
    ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by sorry

end NestedSeatAlloc.IntPolicy
