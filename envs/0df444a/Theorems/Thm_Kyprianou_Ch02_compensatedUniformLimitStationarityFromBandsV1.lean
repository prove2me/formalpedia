-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedUniformLimitStationarityFromBandsV1
-- name    : Kyprianou.Ch02.compensatedUniformLimitStationarityFromBandsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T20:50:25.348195+00:00
-- url     : https://prove2.me/theorems/de6a5d23-2304-4bb0-a05d-1da3457898dd
-- title:
--   Stationary increments inherited by a common a.s. uniform limit
-- statement:
--   Transfer the stationarity of all compensated finite-band Lévy increments to any process admitting almost-sure uniform convergence along strictly decreasing deterministic cutoffs on each finite horizon. For each s,h choose one subsequence for T>s+h; pass equality of increment distributions to the limit using bounded continuous test functions and convergence in distribution.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, limit of compensated Poisson increments

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem compensatedUniformLimitStationarityFromBandsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hzero : M 0 = fun _ => 0)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ))
    (hbands : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ProbabilityTheory.HasStationaryIncrements
        (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε) P) :
    ProbabilityTheory.HasStationaryIncrements M P
    := by sorry
end Kyprianou.Ch02
