-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeft_stoppedValuesPathwiseLimitV1
-- name    : Kyprianou.Ch03.quasiLeft_stoppedValuesPathwiseLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:24:19.13728+00:00
-- url     : https://prove2.me/theorems/05b55137-03ac-47e1-bc5e-ec6824fc7edc
-- title:
--   Lemma 3.2: existence of the pathwise stopped-value limit
-- statement:
--   On finite T, monotone clocks either hit T and are eventually constant, or stay strictly below T, in which case the càdlàg left limit exists. This is purely pathwise and does not identify the limit.
-- source:
--   Kyprianou (2006), Lemma 3.2; reduction of e40f7821-bc5b-415b-9859-f876418451d9.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.quasiLeft_stoppedValuesPathwiseLimitV1
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
    ∀ᵐ omega : Omega ∂ P.restrict {omega : Omega | T omega ≠ ⊤},
      ∃ l : Real, Tendsto (fun n => X (timeTn n omega) omega) atTop (nhds l) := by
  sorry
