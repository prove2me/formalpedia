-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightIntegralUnitLimit
-- name    : Kyprianou.Ch08.StageB.actualHeightIntegralUnitLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:48:36.278423+00:00
-- url     : https://prove2.me/theorems/0ddc9d31-a2da-44ae-9ee4-037e25febe81
-- title:
--   Excursion height: actual discounted no-drawdown expectation tends to one at infinite threshold
-- statement:
--   For every genuine spectrally negative Lévy process and zero or positive discount, as the allowed drawdown height tends to infinity the original normalized discounted unit-upcrossing expectation tends to one. Requires handling infinite passage times and proving the unrestricted first-passage transform without substituting an abstract excursion measure.
-- source:
--   Kyprianou (2006) Lemma 8.2, printed p220, original physical PDF p228. These are the exact second and third clauses of existing connected child ee3350ad-787b-4c66-9ad7-f36a3844271a. Completing them and proving monotonicity by measure restriction proves that child, which has accepted mission graph edge through integral core 2009363d.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightIntegralUnitLimit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto
      (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
      Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      atTop (nhds 1) := by
  sorry
