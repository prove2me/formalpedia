-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actualHeightIntegralMonotoneAndLimits
-- name    : Kyprianou.Ch08.StageB.actualHeightIntegralMonotoneAndLimits
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T09:40:18.123082+00:00
-- url     : https://prove2.me/theorems/ee3350ad-787b-4c66-9ad7-f36a3844271a
-- title:
--   Lemma 8.2: monotonicity, unit-height limit and strict-left continuity of actual drawdown expectation
-- statement:
--   For every genuine spectrally negative Lévy law, discount rate q at least zero and corresponding source scale family, the original discounted no-drawdown-before-unit-upcrossing integral is nondecreasing as the drawdown threshold increases, tends to one as the threshold increases without bound, and is continuous from strictly smaller thresholds at each positive height. These three stochastic path-law obligations retain the original event, discount, boundary conventions and all quantified source parameters. Combined with the separately proved strict positivity, and a pinned order-topology equivalence that turns strict-left limits into closed-left continuity, the three clauses imply the existing source-exact integral core.
-- source:
--   Kyprianou (2006), Lemma 8.2, printed p.220, original physical PDF p.228, original source result 4cc4a403-8950-4d81-b07d-92e8a8c0dad6. This intermediate child isolates the three path-law obligations in open integral core 2009363d-eef9-4af6-8fe2-05d306fd4366, which is connected to the original mission graph via the accepted excursion-law decomposition. Neither an abstract substitute excursion measure nor deprecated integral core fa1082de may be used.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actualHeightIntegralMonotoneAndLimits
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    MonotoneOn
      (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      (Set.Ioi 0) ∧
    Tendsto
      (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
        Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
      atTop (nhds 1) ∧
    (∀ y : ℝ, 0 < y →
      Tendsto
        (fun h => (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 h ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X 1 y ω},
          Real.exp (Phi ψ q * 1) * discountedAt q (tauPlus D.X 1 ω) ∂P))) := by
  sorry
