-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitHasIndependentIncrementsV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpUniformLimitHasIndependentIncrementsV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:45:31.095149+00:00
-- url     : https://prove2.me/theorems/8fd675ad-3245-4d0d-aa78-228e70255e3b
-- title:
--   Theorem 2.10: independent increments of the compensated small-jump uniform limit
-- statement:
--   Transfer joint independence of disjoint finite-band Poisson counts to a deterministic-subsequence uniform-in-probability limit. Use bounded measurable characteristic functions or independence closure of finite-dimensional vectors.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, finite-band limit of increments

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
theorem compensatedSmallJumpUniformLimitHasIndependentIncrementsV1
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
                    M t ω| < δ)) :
    ProbabilityTheory.HasIndependentIncrements M P
    := by sorry
end Kyprianou.Ch02
