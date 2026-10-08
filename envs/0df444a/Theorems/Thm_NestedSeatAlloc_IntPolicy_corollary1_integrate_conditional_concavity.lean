-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_corollary1_integrate_conditional_concavity
-- name    : NestedSeatAlloc.IntPolicy.corollary1_integrate_conditional_concavity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T12:35:50.405238+00:00
-- url     : https://prove2.me/theorems/4204a6a5-95d4-4ce8-a739-2e52d3e9523a
-- title:
--   Independence transfers conditional concavity to expected revenue
-- statement:
--   In the independent nonnegative seat model, if fixing every nonnegative next-class demand gives a concave conditional revenue function, then expected revenue after adding that class is concave.
-- source:
--   Source-faithful measure-theoretic child of Corollary 1 (5a3801ae-82a6-44d7-8f5f-8c951b11140a): use independence of the finite prefix demand vector and X_{k+1} to identify the joint law with the product law, rewrite by pushforward integration, and integrate the fixed-demand concavity inequality under the law of X_{k+1}.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem corollary1_integrate_conditional_concavity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p) (k : ℕ)
    (hcond : ∀ y : ℝ, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) :
    ConcaveOn ℝ (Set.Ici 0) (expRevenue P X f p (k + 1)) := by sorry

end NestedSeatAlloc.IntPolicy
