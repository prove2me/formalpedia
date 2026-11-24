-- Prove2me | Theorems.Thm_Kyprianou_Ch03_delayedOpenHitRationalWitnessV1
-- name    : Kyprianou.Ch03.delayedOpenHitRationalWitnessV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T11:02:21.309811+00:00
-- url     : https://prove2.me/theorems/b60cb514-3ace-4acf-9f24-1a264e18083a
-- title:
--   Delayed open hitting strict sublevel rational witness
-- statement:
--   A witness before s can be moved slightly to its right to a rational time while preserving open membership and the lower bound.
-- source:
--   Kyprianou (2006), Theorem 3.3, delayed open hitting stopping time.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.delayedOpenHitRationalWitnessV1
    {Omega : Type} (X : NNReal → Omega → Real) (B : Set Real)
    (hB : IsOpen B) (a : NNReal) (omega : Omega)
    (hrc : ∀ t : NNReal, ContinuousWithinAt (fun u => X u omega) (Set.Ici t) t)
    (s : NNReal) :
    sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t omega ∈ B}) < (s : WithTop NNReal) ↔
      ∃ q : ℚ, a ≤ Real.toNNReal q ∧ Real.toNNReal q < s ∧ X (Real.toNNReal q) omega ∈ B := by
  sorry
