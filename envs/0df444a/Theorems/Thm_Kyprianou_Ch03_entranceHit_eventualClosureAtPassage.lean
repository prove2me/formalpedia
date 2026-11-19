-- Prove2me | Theorems.Thm_Kyprianou_Ch03_entranceHit_eventualClosureAtPassage
-- name    : Kyprianou.Ch03.entranceHit_eventualClosureAtPassage
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T14:57:08.530859+00:00
-- url     : https://prove2.me/theorems/54c2f05c-922e-4034-a938-073236e62c7c
-- title:
--   Theorem 3.3 source clause 3
-- statement:
--   Exact independently quantified clause 3 of Theorem 3.3. All original hypotheses and process domains are retained.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Theorem 3.3

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem entranceHit_eventualClosureAtPassage
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
    (∀ᵐ omega : Omega ∂ P,
      (firstEntranceTime X B omega != ⊤ ->
        X (entranceTime omega) omega ∈ closure B) ∧
      (firstHittingTime X B omega != ⊤ ->
        X (hittingTime omega) omega ∈ closure B)) := by
  sorry

end Kyprianou.Ch03
