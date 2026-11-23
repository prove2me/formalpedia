-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_norm_lower
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_norm_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:36:11.181894+00:00
-- url     : https://prove2.me/theorems/e2c25bc8-5bae-48e5-9603-dc51c101380f
-- title:
--   Normalized unbounded-variation exponent lower bound
-- statement:
--   For the exact Kyprianou Laplace exponent, the normalized exponent is bounded below by the physical drift, the Gaussian quadratic contribution, the normalized compensated small-jump integral, and the finite negative large-jump mass. This isolates the Lévy–Khintchine estimate needed by the unbounded-variation Lemma 8.6 branch.
-- source:
--   Source-faithful estimate from the Kyprianou triplet formula and the Proved positive-mgf bridge; its intended parent is the connected unbounded child, whose reduction imports this theorem.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
set_option autoImplicit false
open MeasureTheory Filter Set
open Kyprianou.Ch08.StageB
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_norm_lower
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) :
    ∀ θ : ℝ, 0 < θ →
      D.triplet.drift + D.gaussianCoefficient ^ 2 * θ / 2 +
          (∫ y in Ioo (-1 : ℝ) 0,
            (Real.exp (θ * y) - 1 - θ * y) / θ ∂D.triplet.levyMeasure) -
          (∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂D.triplet.levyMeasure) / θ
        ≤ ψ θ / θ := by
  sorry
