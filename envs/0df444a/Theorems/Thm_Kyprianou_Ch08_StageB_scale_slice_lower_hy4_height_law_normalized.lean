-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_scale_slice_lower_hy4_height_law_normalized
-- name    : Kyprianou.Ch08.StageB.scale_slice_lower_hy4_height_law_normalized
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:41:47.233809+00:00
-- url     : https://prove2.me/theorems/2378af01-d862-46bd-a546-1de8b2cc2f30
-- title:
--   Normalized height law at level l
-- statement:
--   The actual height law at (d,l), divided by the positive factor exp(Phi(q)d), identifies the no-drawdown discounted integral with the source exponential at tail l.
-- source:
--   Source-faithful algebraic child of scale_slice_lower_hy4 (795c944f); isolates the upper-slice normalization calculation.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.scale_slice_lower_hy4_height_law_normalized
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (n : Measure ℝ) (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d l ω}, discountedAt q (tauPlus D.X d ω) ∂P) =
        Real.exp (-(d * (Phi ψ q + (n (Set.Ici l)).toReal))) := by
  sorry
