-- Prove2me | Theorems.Thm_Kyprianou_Ch05_rawPredictableLeftVersionPositiveV1
-- name    : Kyprianou.Ch05.rawPredictableLeftVersionPositiveV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T18:45:33.9944+00:00
-- url     : https://prove2.me/theorems/37995e08-7f49-4018-a4ff-26abc1539a9f
-- title:
--   Predictable pre-jump version of a nonnegative monotone adapted process on a raw filtration
-- statement:
--   Sample the adapted process strictly before each positive time on the proved Chapter 4 grid. The liminf of its nonnegative samples is predictable even on the raw filtration and equals the left limit on the common monotone full-measure event.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.rawPredictableLeftVersionPositiveV1
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega)
    (F : Filtration NNReal inferInstance) (X : NNReal → Omega → ℝ)
    (hX : Adapted F X)
    (hreg : ∀ᵐ w ∂P, Monotone (fun t => X t w) ∧ X 0 w = 0) :
    ∃ V : NNReal → Omega → ℝ, Measurable[F.predictable] (Function.uncurry V) ∧
      ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t → V t w = Function.leftLim (fun s => X s w) t := by
  sorry
