-- Prove2me | Theorems.Thm_Kyprianou_Ch03_quasiLeft_denseShiftOscillationV1
-- name    : Kyprianou.Ch03.quasiLeft_denseShiftOscillationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:53:37.673237+00:00
-- url     : https://prove2.me/theorems/57ede920-a63c-4df9-8724-a672b0eaa8af
-- title:
--   Dense sampling of shifted right-continuous paths
-- statement:
--   By right continuity at a+u, the strict half-threshold holds on a short right interval in the lag variable. Intersect the open interval inside (u,delta) with the dense set S.
-- source:
--   Kyprianou (2006), Lemma 3.2; parent a6f477ce-ae19-410a-b862-1deace8d82c9.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch03
set_option autoImplicit false

theorem Kyprianou.Ch03.quasiLeft_denseShiftOscillationV1
    (f : NNReal → Real) (hf : ProbabilityTheory.IsCadlag f)
    (S : Set NNReal) (hS : Dense S)
    (a delta : NNReal) (eps : Real) (heps : 0 < eps)
    (u : NNReal) (hu : u < delta)
    (hbig : eps ≤ dist (f (a + u)) (f a)) :
    ∃ v ∈ S, v < delta ∧ eps / 2 < |f (a + v) - f a| := by
  sorry
