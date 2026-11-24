-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovAtExtendedStoppingTime
-- name    : Kyprianou.Ch03.strongMarkovAtExtendedStoppingTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:37:14.207834+00:00
-- url     : https://prove2.me/theorems/2623fefc-be31-45fd-9189-b00f2e50b331
-- title:
--   Theorem 3.1: strong Markov property at extended stopping times
-- statement:
--   At any potentially infinite stopping time of a right-continuous filtration for which the Levy process is adapted and its increments independent of past information, on the finite-time event the entire post-stopping increment path has the original process law and is independent of every stopped-past event. The claim is given as a product law for the stopped-event indicator and future path. The filtration is the completed natural filtration of this Levy process, and right-continuity follows from the separately formalised Exercise 3.1.
-- source:
--   Kyprianou (2006), Chapter 3, 3.1, pp. 67-71.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem strongMarkovAtExtendedStoppingTime
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega -> WithTop NNReal)
    (hTau : IsStoppingTime F tau)
    (finiteTime : Omega -> NNReal)
    (hFiniteTime : forall omega, tau omega != ⊤ ->
      tau omega = (finiteTime omega : WithTop NNReal)) :
    forall A : Set Omega,
      (forall s : NNReal,
        MeasurableSet[F s]
          (Set.inter A {omega : Omega | tau omega <= (s : WithTop NNReal)})) ->
      Measure.map
        (fun omega : Omega =>
          (Set.indicator A (fun _ : Omega => (1 : Real)) omega,
           fun u : NNReal =>
             X (finiteTime omega + u) omega - X (finiteTime omega) omega))
        (P.restrict {omega : Omega | tau omega != ⊤}) =
      (Measure.map
        (Set.indicator A (fun _ : Omega => (1 : Real)))
        (P.restrict {omega : Omega | tau omega != ⊤})).prod
        (Measure.map (fun omega : Omega => fun u : NNReal => X u omega) P) := by
  sorry
end Kyprianou.Ch03
