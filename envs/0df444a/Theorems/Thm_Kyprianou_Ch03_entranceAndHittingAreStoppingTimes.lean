-- Prove2me | Theorems.Thm_Kyprianou_Ch03_entranceAndHittingAreStoppingTimes
-- name    : Kyprianou.Ch03.entranceAndHittingAreStoppingTimes
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:38:08.699387+00:00
-- url     : https://prove2.me/theorems/77d46683-a47a-432c-a1bc-c5e41701dd17
-- title:
--   Theorem 3.3: first entrance and first hitting of open or closed sets
-- statement:
--   For an open or closed B, the first entrance (t>=0) and first hitting (t>0) are stopping times under the right-continuous Levy filtration hypotheses. At a finite entrance or hit, the process position lies in closure(B). Representatives of the finite values are supplied without postulating any boundary membership. The filtration is the completed natural filtration of this Levy process, and right-continuity follows from the separately formalised Exercise 3.1.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.3, pp. 71-73.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem entranceAndHittingAreStoppingTimes
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsOpen B ∨ IsClosed B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    IsStoppingTime F (firstEntranceTime X B) ∧
    IsStoppingTime F (firstHittingTime X B) ∧
    (∀ᵐ omega : Omega ∂ P,
      (firstEntranceTime X B omega != ⊤ ->
        X (entranceTime omega) omega ∈ closure B) ∧
      (firstHittingTime X B omega != ⊤ ->
        X (hittingTime omega) omega ∈ closure B)) := by
  sorry
end Kyprianou.Ch03
