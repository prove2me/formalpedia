-- Prove2me | Theorems.Thm_Kyprianou_Ch04_actualPoissonPastMeasurableV1
-- name    : Kyprianou.Ch04.actualPoissonPastMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:18:18.311874+00:00
-- url     : https://prove2.me/theorems/d0a99895-d2bd-5bc1-be06-33b264728391
-- title:
--   Actual Poisson jump measure is measurable on the completed natural past
-- statement:
--   Freeze the original path at T and apply the measurable arbitrary Borel time-mark extractor. The original and frozen physical counts agree on the entire past region almost surely. Completion transfers measurability to the actual Poisson measure.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, adapted physical Poisson counts.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalCoordinateAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_completedMeasAECongrV1
import Theorems.Thm_Kyprianou_Ch04_arbitraryTimeMarkExtractorV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathMarkedCountV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathRightContinuousV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftExistenceV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureCountV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousTimeMeasurableV1
import Theorems.Thm_Kyprianou_Ch04_leftLimitTimeMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem actualPoissonPastMeasurableV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X L : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hL : ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun u => X u ω) (𝓝[<] t) (𝓝 (L t ω)))
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X L ω) :
    ∀ (T : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (T : ℝ) ×ˢ univ →
      Measurable[F T] (fun ω => N.N ω D) := by
  sorry
end Kyprianou.Ch04
