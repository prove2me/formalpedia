-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_locator_geometry
-- name    : Kyprianou.Ch04.ito43_cutoff_finite_locator_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:02:14.478058+00:00
-- url     : https://prove2.me/theorems/8f9b6f43-f43d-4906-b66b-423bb679fd88
-- title:
--   Finite jump times have separated right-closed grid cells
-- statement:
--   Choose a locator from the existing Avram shrinking-cell theorem for n plus one and shift the index back by one. The finite set of right endpoints converges to distinct jump times, so the locator is eventually injective.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_finite_locator_geometry (T : NNReal) (S : Finset NNReal)
    (hS : ∀ s ∈ S, 0 < s ∧ s ≤ T) :
    ∃ j : NNReal → ℕ → ℕ,
      (∀ᶠ n : ℕ in atTop, ∀ s ∈ S,
        j s n < n ∧ T*(j s n : NNReal)/(n:NNReal) < s ∧
        s ≤ T*((j s n+1 : ℕ):NNReal)/(n:NNReal)) ∧
      (∀ᶠ n : ℕ in atTop, Set.InjOn (fun s => j s n) (S : Set NNReal)) := by sorry
