-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_esscher_coefficient_at_root
-- name    : Kyprianou.Ch08.StageB.p2m810_esscher_coefficient_at_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T18:05:49.854716+00:00
-- url     : https://prove2.me/theorems/440cce0f-8396-480b-b4cf-237cbfda7427
-- title:
--   Esscher boundary coefficient equals the derivative at the positive-discount root
-- statement:
--   Esscher boundary coefficient equals the derivative at the positive-discount root
-- source:
--   Kyprianou (2006), Exercise 8.10(iv)

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_C
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem Kyprianou.Ch08.StageB.p2m810_esscher_coefficient_at_root
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 < q) :
    esscherDownCoefficient ψ (Phi ψ q) q = deriv ψ (Phi ψ q) := by
  sorry
