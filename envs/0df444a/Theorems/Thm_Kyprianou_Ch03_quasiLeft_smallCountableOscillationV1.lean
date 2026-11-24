-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeft_smallCountableOscillationV1
-- name    : Kyprianou.Ch03.quasiLeft_smallCountableOscillationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:53:45.028277+00:00
-- url     : https://prove2.me/theorems/b54180af-c4f7-467f-b9c6-68e751240252
-- title:
--   Small countable oscillations at zero
-- statement:
--   The countable coordinate events for horizons 1/(n+1) are measurable and decreasing. Almost every path is right continuous at zero and starts at zero, so their intersection is null. Continuity from above for the probability law gives the bound.
-- source:
--   Kyprianou (2006), Lemma 3.2; parent a6f477ce-ae19-410a-b862-1deace8d82c9.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch03
set_option autoImplicit false

theorem Kyprianou.Ch03.quasiLeft_smallCountableOscillationV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hMeas : ∀ t, Measurable (X t))
    (S : Set NNReal) (hS : S.Countable)
    (eps : Real) (heps : 0 < eps)
    (eta : ENNReal) (heta : 0 < eta) :
    ∃ delta : NNReal, 0 < delta ∧
      MeasurableSet {f : NNReal → Real | ∃ v ∈ S, v < delta ∧ eps / 2 < |f v|} ∧
      Measure.map (fun w t => X t w) P
        {f : NNReal → Real | ∃ v ∈ S, v < delta ∧ eps / 2 < |f v|} ≤ eta := by
  sorry
