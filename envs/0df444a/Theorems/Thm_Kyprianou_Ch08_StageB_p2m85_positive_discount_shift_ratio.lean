-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_positive_discount_shift_ratio
-- name    : Kyprianou.Ch08.StageB.p2m85_positive_discount_shift_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T13:25:12.896923+00:00
-- url     : https://prove2.me/theorems/7d9530f2-c220-4134-a01d-22961fb3234f
-- title:
--   Positive-discount scale ratio at infinity
-- statement:
--   At strictly positive discount the shifted q-scale ratio tends to the exponential of minus the right root times the shift.
-- source:
--   Kyprianou (2006), Exercise 8.5(i), positive-discount case of the third clause.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.p2m85_positive_discount_shift_ratio
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q x : ℝ) (hq : 0 < q) :
    Tendsto (fun a : ℝ => W q (a-x) / W q a)
      atTop (𝓝 (Real.exp (-Phi ψ q * x))) := by
  sorry
