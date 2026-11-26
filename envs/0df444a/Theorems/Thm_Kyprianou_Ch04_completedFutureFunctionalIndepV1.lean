-- Prove2me | Theorems.Thm_Kyprianou_Ch04_completedFutureFunctionalIndepV1
-- name    : Kyprianou.Ch04.completedFutureFunctionalIndepV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:52.358524+00:00
-- url     : https://prove2.me/theorems/73b41baa-3f9e-5992-a8c2-6b3c175f3d0d
-- title:
--   Future path functional independence from completed natural filtration
-- statement:
--   Future path functional independence from completed natural filtration
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem completedFutureFunctionalIndepV1 {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (s : NNReal) (G : (NNReal → ℝ) → E) (hG : Measurable G)
    (W : Ω → E)
    (hW : W =ᵐ[P] fun ω => G (fun u : NNReal => X (s+u) ω - X s ω)) :
    Indep (MeasurableSpace.comap W inferInstance) (F s) P := by
  sorry
end Kyprianou.Ch04
