-- Prove2me | Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
-- name    : Kyprianou.Ch03.completedNaturalLevyFiltrationRightContinuous
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:36:42.860598+00:00
-- url     : https://prove2.me/theorems/c428a15c-6267-46ca-ac3c-73270db83e41
-- title:
--   Exercise 3.1: right-continuity of the completed natural Levy filtration
-- statement:
--   A completed natural filtration F of a Levy process X is right continuous. Its specific completed-natural-filtration condition prevents incorrectly generalising right-continuity to arbitrary processes.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.1, printed p. 83.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem completedNaturalLevyFiltrationRightContinuous
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hCompleted : IsCompletedNaturalFiltration P X F) :
    F.IsRightContinuous := by
  sorry

end Kyprianou.Ch03
