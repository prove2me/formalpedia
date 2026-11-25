-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineFderivIntegrableV1
-- name    : Kyprianou.Ch04.exercise42LipschitzAffineFderivIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:58:02.686888+00:00
-- url     : https://prove2.me/theorems/9b4db708-740b-5374-b39d-a18df487ff57
-- title:
--   Componentwise fderiv integrability on a Lipschitz-affine segment
-- statement:
--   Each fixed directional fderiv component is integrable on a compact Lipschitz-affine segment when the first coordinate is nonnegative and strictly positive except possibly at its left endpoint.
-- source:
--   Lipschitz Stieltjes calculus support for Kyprianou (2006), Ch04 Exercise 4.2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvFullFderivEqWithinPositiveV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise42LipschitzAffineFderivIntegrableV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hNonneg : ∀ s ∈ Icc l r, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s)
    (v : ℝ × ℝ) :
    IntervalIntegrable
      (fun s : ℝ => fderiv ℝ f (U s, a + c * s) v) volume l r := by
  sorry
