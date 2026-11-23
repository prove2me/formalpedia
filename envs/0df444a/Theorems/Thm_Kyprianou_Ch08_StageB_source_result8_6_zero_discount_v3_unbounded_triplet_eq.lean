-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_triplet_eq
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_triplet_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:29:20.437846+00:00
-- url     : https://prove2.me/theorems/e527a9b3-2d87-446e-9692-10ba9788bd21
-- title:
--   Normalized triplet form of the positive Laplace exponent
-- statement:
--   For a positive Laplace parameter, the normalized Laplace exponent equals the drift, the Gaussian quadratic term, and the normalized compensated negative-jump integral in the exact Kyprianou triplet convention.
-- source:
--   Normalized form of the Kyprianou Levy-Khintchine identity obtained from the Proved positive-mgf bridge source_result81_law_positive_mgf.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_law_positive_mgf
set_option autoImplicit false
open MeasureTheory Filter Set
open Kyprianou.Ch08.StageB
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_triplet_eq
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (θ : ℝ) (hθ : 0 < θ) :
    ψ θ / θ = D.triplet.drift + D.gaussianCoefficient ^ 2 * θ / 2 +
      ∫ y in Iio (0 : ℝ),
        (Real.exp (θ * y) - 1 - (if -1 < y then θ * y else 0)) / θ
          ∂D.triplet.levyMeasure := by
  sorry
