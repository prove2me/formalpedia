-- Prove2me | Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime_of_isOpen
-- name    : Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime_of_isOpen
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T03:32:55.435139+00:00
-- url     : https://prove2.me/theorems/633108c0-74df-4670-9b17-a13f7dfacb83
-- title:
--   First hitting time of an open set is a stopping time
-- statement:
--   Let $X$ be a Lévy process on the completed natural filtration $\mathcal{F}$ of $X$, and let $B\subset\mathbb{R}$ be **open**. Write $\tau_B^+=\inf\{t>0:X_t\in B\}$ (with the usual $\infty$ convention).
--
--   Then $\tau_B^+$ is an $\mathcal{F}$-stopping time.
--
--   This is the open-set case of Kyprianou Theorem 3.3 (hitting clause). The argument uses càdlàg paths, openness of $B$, and right-continuity of the completed natural filtration (Exercise 3.1).
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Theorem 3.3 (first-hitting stopping-time clause, open/closed case split)

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem entranceHit_firstHittingIsStoppingTime_of_isOpen
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real)
    (hB : IsOpen B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    IsStoppingTime F (firstHittingTime X B) := by
  sorry

end Kyprianou.Ch03
