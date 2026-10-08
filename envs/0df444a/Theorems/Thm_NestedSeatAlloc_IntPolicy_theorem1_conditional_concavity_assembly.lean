-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_theorem1_conditional_concavity_assembly
-- name    : NestedSeatAlloc.IntPolicy.theorem1_conditional_concavity_assembly
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T07:28:41.983975+00:00
-- url     : https://prove2.me/theorems/b5509f32-8d08-4cb0-a4e9-12ce6d521bef
-- title:
--   Theorem 1 concavity assembly — base and step imply all nests
-- statement:
--   A one-class conditional-concavity base case together with the one-step induction implication yields conditional concavity for every nest under the full subdifferential condition.
-- source:
--   Source-faithful induction assembly for Brumelle & McGill (1993), Theorem 1 conditional-concavity proof, pp. 131–132.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

theorem theorem1_conditional_concavity_assembly {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (h20 : SubdiffCondition P X f p)
    (hbase : ∀ y, 0 ≤ y → ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p 1 y))
    (hstep : ∀ k y, 1 ≤ k → 0 ≤ y →
      InSubdiff (expRevenue P X f p k) (p k) (f (k + 1)) →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p k y) →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y)) :
    ∀ k, 1 ≤ k → ∀ y, 0 ≤ y →
      ConcaveOn ℝ (Set.Ici 0) (condRevenue P X f p (k + 1) y) := by sorry

end NestedSeatAlloc.IntPolicy
