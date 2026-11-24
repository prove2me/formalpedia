-- Prove2me | Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime_of_isOpen_of_rightCont
-- name    : Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime_of_isOpen_of_rightCont
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-24T03:42:12.852195+00:00
-- url     : https://prove2.me/theorems/2e8e30d3-a2d9-4be9-bd87-f43f60ac147b
-- title:
--   Open first hitting is a stopping time under right continuity
-- statement:
--   Let $X$ be a Lévy process whose completed natural filtration $\mathcal{F}$ is assumed **right continuous**, and let $B\subset\mathbb{R}$ be open. Write $\tau_B^+=\inf\{t>0:X_t\in B\}$.
--
--   Then $\tau_B^+$ is an $\mathcal{F}$-stopping time.
--
--   This is the open-debut core of Kyprianou Theorem 3.3 (hitting clause), with Exercise 3.1 (right continuity) factored out as a hypothesis. The remaining work uses càdlàg paths and openness of $B$ to identify $\{\tau_B^+ < t\}$ with a countable union of events $\{X_q\in B\}$ and pass to $\{\tau_B^+ \le t\}$ via right continuity.
-- source:
--   Kyprianou (2006), first edition, Chapter 3, Theorem 3.3 open-hitting case with right continuity hypothesized (Exercise 3.1 factored out)

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem entranceHit_firstHittingIsStoppingTime_of_isOpen_of_rightCont
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real)
    (hB : IsOpen B)
    (hRC : F.IsRightContinuous)
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
