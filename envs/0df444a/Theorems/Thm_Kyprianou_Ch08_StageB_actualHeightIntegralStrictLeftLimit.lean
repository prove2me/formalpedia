-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightIntegralStrictLeftLimit
-- name    : Kyprianou.Ch08.StageB.actualHeightIntegralStrictLeftLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T09:48:32.035425+00:00
-- url     : https://prove2.me/theorems/cade7bf0-28cb-43f9-b50a-18cc573d5092
-- title:
--   Excursion height: actual discounted no-drawdown expectation is continuous from strictly below
-- statement:
--   For every genuine spectrally negative Lévy process and zero or positive discount, the original discounted no-drawdown-before-unit-upcrossing integral has its correct left-sided limit at each positive height. The strict pathwise condition and passage endpoint, including height approached but not attained, must be handled; no continuity assumption on the jump-height distribution is added.
-- source:
--   Kyprianou (2006) Lemma 8.2, printed p220, original physical PDF p228. These are the exact second and third clauses of existing connected child ee3350ad-787b-4c66-9ad7-f36a3844271a. Completing them and proving monotonicity by measure restriction proves that child, which has accepted mission graph edge through integral core 2009363d.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightIntegralStrictLeftLimit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ y : ℝ, 0 < y →
      Tendsto
        (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
      Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P)) := by
  sorry
