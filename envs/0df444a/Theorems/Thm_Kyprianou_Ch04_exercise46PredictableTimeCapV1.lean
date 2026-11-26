-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PredictableTimeCapV1
-- name    : Kyprianou.Ch04.exercise46PredictableTimeCapV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T23:36:39.898341+00:00
-- url     : https://prove2.me/theorems/75bb6a89-4bfe-4619-83a0-89f452fed5eb
-- title:
--   Deterministic compact time cap is predictable
-- statement:
--   Decompose the deterministic time cap into the initial singleton and a predictable interval.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PredictableTimeCapV1
    {Omega : Type} [MeasurableSpace Omega]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (T : NNReal) :
    MeasurableSet[G.predictable] {p : NNReal × Omega | p.1 ≤ T} := by
  sorry
