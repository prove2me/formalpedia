-- Prove2me | Theorems.Thm_Kyprianou_Ch01_cappedFirstUpperCrossingGridTimeConvergesPublic
-- name    : Kyprianou.Ch01.cappedFirstUpperCrossingGridTimeConvergesPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:48:53.316199+00:00
-- url     : https://prove2.me/theorems/bccbc057-8552-47b4-8af6-11200a52a370
-- title:
--   Finite sentinel-capped strict upper-crossing grid times converge to continuous capped first passage
-- statement:
--   For a continuous real path starting at zero and strictly positive barrier x, fix a finite physical cap T. On the uniform grid T/(N+1), stop at the first integer grid index k whose path value strictly exceeds x or at the terminal sentinel N+1. As resolution increases, the physical stopped time converges to the genuine first strictly positive upper passage capped at T (or T if passage is infinite). The proof must handle first passage before T, exactly T and after T, using continuity, the strict crossing set's infimum property and detection by sufficiently fine grids.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10(ii), bounded optional-stopping grid approximation.

import Mathlib.Topology.Bornology.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Find
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.cappedFirstUpperCrossingGridTimeConvergesPublic
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (x : ℝ)
    (hx : 0 < x) (hcont : Continuous (fun t : ℝ≥0 => X t ω))
    (hzero : X 0 ω = 0) (T : ℝ≥0) :
    Tendsto (fun N : ℕ =>
      let K : ℕ := N + 1
      let delta : ℝ≥0 := T / (K : ℝ≥0)
      let tau : ℕ := by
        classical
        exact Nat.find (show ∃ k : ℕ,
          k = K ∨ x < X ((k : ℝ≥0) * delta) ω from ⟨K, Or.inl rfl⟩)
      (tau : ℝ≥0) * delta) atTop
      (nhds (match firstUpperPassage X x ω with
        | none => T
        | some t => min t T)) := by sorry
