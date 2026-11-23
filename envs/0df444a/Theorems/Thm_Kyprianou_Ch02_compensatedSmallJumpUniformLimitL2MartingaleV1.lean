-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitL2MartingaleV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpUniformLimitL2MartingaleV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T19:42:21.021804+00:00
-- url     : https://prove2.me/theorems/55d1ea15-5edf-4886-8c50-04e78b44b8e6
-- title:
--   Theorem 2.10: L2 martingale limit under the completed natural Poisson filtration
-- statement:
--   Prove adaptation, martingale conditional expectations and square-integrability of the common uniform limit, using the completed Poisson filtration and finite-band L2/isometry estimates.
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
theorem compensatedSmallJumpUniformLimitL2MartingaleV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
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
    MeasureTheory.Martingale M ℱ P ∧
    ∀ t : ℝ≥0, MemLp (M t) 2 P
    := by sorry
end Kyprianou.Ch02
