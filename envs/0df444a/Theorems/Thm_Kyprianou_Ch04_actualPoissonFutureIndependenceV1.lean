-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
-- name    : Kyprianou.Ch04.actualPoissonFutureIndependenceV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T23:58:15.265869+00:00
-- url     : https://prove2.me/theorems/782fa041-e3f7-5147-a9ac-6d47fd27707d
-- title:
--   Actual Lévy Poisson measure future independence from completed natural past
-- statement:
--   Actual Lévy Poisson measure future independence from completed natural past
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualPoissonFutureIndependenceV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u ω) (𝓝[<] t) (𝓝 (L t ω)))
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X L ω) :
    Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N := by
  sorry
end Kyprianou.Ch04
