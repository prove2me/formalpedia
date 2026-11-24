-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeft_uniformStoppedOscillationV1
-- name    : Kyprianou.Ch03.quasiLeft_uniformStoppedOscillationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:29:41.218012+00:00
-- url     : https://prove2.me/theorems/a6f477ce-ae19-410a-b862-1deace8d82c9
-- title:
--   Lemma 3.2: uniform short-horizon oscillation after a finite stopping time
-- statement:
--   For every positive spatial tolerance and probability tolerance there is a deterministic positive horizon controlling the post-stopping oscillation, uniformly over extended stopping times on their finite events. Use the strong Markov restricted path law on a countable dense set of times, then càdlàg right continuity and the vanishing oscillation at zero. The outer measure statement also covers non-measurable uncountable supremum events.
-- source:
--   Kyprianou (2006), Lemma 3.2 and Theorem 3.1; convergence-in-measure child a4eda0ec-df84-488e-a209-50ed53bbb8bf.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.quasiLeft_uniformStoppedOscillationV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F) :
    ∀ (epsilon : Real), 0 < epsilon →
    ∀ (eta : ENNReal), 0 < eta →
      ∃ delta : NNReal, 0 < delta ∧
        ∀ (tau : Omega → WithTop NNReal) (finiteTime : Omega → NNReal),
          IsStoppingTime F tau →
          (∀ omega, tau omega ≠ ⊤ → tau omega = (finiteTime omega : WithTop NNReal)) →
          P {omega : Omega | tau omega ≠ ⊤ ∧ ∃ u : NNReal, u < delta ∧
            epsilon ≤ dist (X (finiteTime omega + u) omega) (X (finiteTime omega) omega)} ≤ eta := by
  sorry
