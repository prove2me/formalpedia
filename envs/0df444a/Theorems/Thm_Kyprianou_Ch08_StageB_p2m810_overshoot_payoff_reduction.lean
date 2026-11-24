-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_overshoot_payoff_reduction
-- name    : Kyprianou.Ch08.StageB.p2m810_overshoot_payoff_reduction
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T18:05:55.667962+00:00
-- url     : https://prove2.me/theorems/ed6dd611-21ee-4580-a340-6d8e346c2c59
-- title:
--   Positive-discount weighted overshoot transform
-- statement:
--   Positive-discount weighted overshoot transform
-- source:
--   Kyprianou (2006), Exercise 8.10(iv)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m810_overshoot_payoff_reduction
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) (y : ℝ) (hy : 0 < y) :
    deriv (Phi ψ) q * (∫ ω, downOvershootTilt D.X q (Phi ψ q) y ω ∂P) =
      deriv (Phi ψ) q * Real.exp (Phi ψ q * y) - W q y := by
  sorry
