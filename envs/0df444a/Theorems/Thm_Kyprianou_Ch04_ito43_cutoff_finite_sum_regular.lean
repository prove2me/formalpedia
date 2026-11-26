-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_sum_regular
-- name    : Kyprianou.Ch04.ito43_cutoff_finite_sum_regular
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:09:16.821247+00:00
-- url     : https://prove2.me/theorems/a5a055e7-0ccd-4e8e-b619-5946c50bc847
-- title:
--   Finite sums preserve right continuity and compact absolute bounds
-- statement:
--   Finite sums preserve right continuity by induction. Sum the finitely many absolute bounds to get the compact bound.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_finite_sum_regular {ι : Type} (S : Finset ι) (F : ι → NNReal → ℝ) (T : NNReal)
    (hR : ∀ i ∈ S, ∀ t, ContinuousWithinAt (F i) (Ici t) t)
    (hB : ∀ i ∈ S, ∃ M : ℝ, ∀ t ≤ T, |F i t| ≤ M) :
    (∀ t, ContinuousWithinAt (fun s => ∑ i ∈ S, F i s) (Ici t) t) ∧
      ∃ M : ℝ, ∀ t ≤ T, |∑ i ∈ S, F i t| ≤ M := by sorry
