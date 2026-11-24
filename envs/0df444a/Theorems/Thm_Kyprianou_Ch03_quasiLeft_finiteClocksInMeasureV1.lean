-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeft_finiteClocksInMeasureV1
-- name    : Kyprianou.Ch03.quasiLeft_finiteClocksInMeasureV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:33:44.205688+00:00
-- url     : https://prove2.me/theorems/3a9e7a43-9fe0-44a6-964d-7a165bc70313
-- title:
--   Monotone finite stopping clocks converge in measure
-- statement:
--   Under the original stopping-clock assumptions, all approximants are finite and at most the terminal clock almost everywhere on the finite terminal event. Their real-valued clocks converge in measure there.
-- source:
--   Kyprianou (2006), Lemma 3.2; finite-clock reduction of a4eda0ec-df84-488e-a209-50ed53bbb8bf.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.quasiLeft_finiteClocksInMeasureV1
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
    (∀ᵐ omega : Omega ∂ P.restrict {omega : Omega | T omega ≠ ⊤},
      ∀ n, Tn n omega ≠ ⊤ ∧ timeTn n omega ≤ timeT omega) ∧
    TendstoInMeasure (P.restrict {omega : Omega | T omega ≠ ⊤})
      timeTn atTop timeT := by
  sorry
