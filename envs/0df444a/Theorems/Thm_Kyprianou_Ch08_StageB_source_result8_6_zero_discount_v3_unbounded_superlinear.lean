-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_unbounded_superlinear
-- name    : Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_superlinear
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:03:59.197062+00:00
-- url     : https://prove2.me/theorems/46e52bf2-2cc7-4783-ad48-f98494a5d3b4
-- title:
--   Unbounded variation gives superlinear normalized Laplace exponent
-- statement:
--   Under exact non-bounded-variation of the Kyprianou triplet, the normalized Laplace exponent eventually exceeds every real constant. The Gaussian branch uses quadratic dominance; the zero-Gaussian branch uses divergence of normalized compensated negative-jump integrals. The unbounded child imports this theorem to obtain the generic zero-origin condition.
-- source:
--   Source-faithful unbounded-variation growth theorem built from the exact Kyprianou triplet lower bound and Proved generic asymptotic branches; intended parent edge is the connected unbounded child.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Filter Set
open Kyprianou.Ch08.StageB
noncomputable section

theorem Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_unbounded_superlinear
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hnbv : ¬ HasBoundedVariationTriplet D.gaussianCoefficient D.triplet.levyMeasure) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧ ∀ θ : ℝ, β ≤ θ → C < ψ θ / θ := by
  sorry
