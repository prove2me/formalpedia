-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_large_jump_lower
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_large_jump_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:35:46.456144+00:00
-- url     : https://prove2.me/theorems/71c04ef4-434a-497a-b312-d369fc53677c
-- title:
--   Large negative jump lower bound for the compensated kernel
-- statement:
--   For a Levy measure with the quadratic integrability bound and a positive Laplace parameter, the normalized exponential kernel on jumps below -1 is bounded below by minus the finite jump mass divided by the parameter.
-- source:
--   Generic measure-theoretic lower bound extracted from the unbounded-variation Lemma 8.6 proof, using the compensated-jump integrability helper in the prove reduction and positivity of the exponential kernel.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_large_jump_lower
    (μ : Measure ℝ) (hμ : Integrable (fun y : ℝ => min 1 (y ^ 2)) μ)
    (θ : ℝ) (hθ : 0 < θ) :
    -(∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂μ) / θ
      ≤ ∫ y in Iic (-1 : ℝ), (Real.exp (θ * y) - 1) / θ ∂μ := by
  sorry
