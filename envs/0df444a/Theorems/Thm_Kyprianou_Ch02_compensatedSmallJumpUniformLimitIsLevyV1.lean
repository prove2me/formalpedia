-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitIsLevyV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpUniformLimitIsLevyV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:42:20.602455+00:00
-- url     : https://prove2.me/theorems/6d29c2cb-35a6-4827-a55e-ada500739646
-- title:
--   Theorem 2.10: stationary independent-increment càdlàg Lévy limit
-- statement:
--   Transfer independent and stationary Poisson increments and càdlàg regularity to a single small-jump process M from the pointwise-zero and uniform-on-compact almost-sure approximation hypotheses.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, stochastic construction

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
theorem compensatedSmallJumpUniformLimitIsLevyV1
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
    ProbabilityTheory.IsLevyProcess M P
    := by sorry
end Kyprianou.Ch02
