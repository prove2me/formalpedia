-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeft_stoppedValuesInMeasureV1
-- name    : Kyprianou.Ch03.quasiLeft_stoppedValuesInMeasureV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T07:24:16.293863+00:00
-- url     : https://prove2.me/theorems/a4eda0ec-df84-488e-a209-50ed53bbb8bf
-- title:
--   Lemma 3.2: convergence in measure on the finite stopping event
-- statement:
--   Use the strong Markov property at each Tn and a uniform short-horizon oscillation bound from right continuity at zero; split by whether T - Tn exceeds the horizon. Restrict the measure to finite T.
-- source:
--   Kyprianou (2006), Lemma 3.2; reduction of e40f7821-bc5b-415b-9859-f876418451d9.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.quasiLeft_stoppedValuesInMeasureV1
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
    TendstoInMeasure (P.restrict {omega : Omega | T omega ≠ ⊤})
      (fun n omega => X (timeTn n omega) omega) atTop
      (fun omega => X (timeT omega) omega) := by
  sorry
