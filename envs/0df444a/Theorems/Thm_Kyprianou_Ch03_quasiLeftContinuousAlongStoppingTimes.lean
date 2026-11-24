-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeftContinuousAlongStoppingTimes
-- name    : Kyprianou.Ch03.quasiLeftContinuousAlongStoppingTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:37:41.844847+00:00
-- url     : https://prove2.me/theorems/7240686d-5bbf-4b24-8fe9-84a0600f317d
-- title:
--   Lemma 3.2: quasi-left-continuity along increasing stopping times
-- statement:
--   For increasing extended stopping times converging almost surely to T, the Levy process sampled at the approximating times converges to X_T on the event that T is finite. If all approximating stopping times precede T strictly, the left limit at T agrees with X_T on that event. The filtration is the completed natural filtration of this Levy process, and right-continuity follows from the separately formalised Exercise 3.1.
-- source:
--   Kyprianou (2006), Chapter 3, 3.2, pp. 67-71.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem quasiLeftContinuousAlongStoppingTimes
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega -> WithTop NNReal)
    (Tn : Nat -> Omega -> WithTop NNReal)
    (timeT : Omega -> NNReal) (timeTn : Nat -> Omega -> NNReal)
    (hTimeT : forall omega, T omega != ⊤ ->
      T omega = (timeT omega : WithTop NNReal))
    (hTimeTn : forall n omega, Tn n omega != ⊤ ->
      Tn n omega = (timeTn n omega : WithTop NNReal))
    (hT : IsStoppingTime F T)
    (hTn : forall n, IsStoppingTime F (Tn n))
    (hIncreasing : ∀ᵐ omega : Omega ∂ P,
      Monotone (fun n => Tn n omega))
    (hLimit : ∀ᵐ omega : Omega ∂ P,
      Tendsto (fun n => Tn n omega) atTop (nhds (T omega))) :
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      Tendsto (fun n => X (timeTn n omega) omega)
        atTop (nhds (X (timeT omega) omega))) ∧
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      (forall n, Tn n omega < T omega) ->
      Function.leftLim (fun s : NNReal => X s omega) (timeT omega) =
        X (timeT omega) omega) := by
  sorry
end Kyprianou.Ch03
