-- Prove2me | Theorems.Thm_Kyprianou_Ch01_continuousUpperCrossingIoi_iff_rational
-- name    : Kyprianou.Ch01.continuousUpperCrossingIoi_iff_rational
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T21:54:56.157195+00:00
-- url     : https://prove2.me/theorems/39aa2381-44f2-49cd-a2b8-157598aacbec
-- title:
--   Open-horizon strict upper crossing is exactly a countable rational-time crossing for continuous paths
-- statement:
--   For a continuous real path on nonnegative time, it exceeds a strict upper barrier at some time in the open interval (0,u) if and only if it exceeds the same barrier at a positive rational time in (0,u). Forward implication is the already published continuousUpperCrossingRationalWitness, which follows from openness of crossing sets and density of rational times. Reverse is immediate by converting the positive rational into the corresponding nonnegative real time. This exact event-level equivalence is the pathwise component used to prove the continuous first-upper-passage stopping time in the right-continuous natural filtration.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.5 and Exercise 1.6.

import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open Kyprianou.Ch01
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.continuousUpperCrossingIoi_iff_rational
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (u : ℝ≥0) :
    (∃ t : ℝ≥0, 0 < t ∧ t < u ∧ s < X t ω) ↔
    (∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) < (u : ℝ) ∧
      s < X (Real.toNNReal (q : ℝ)) ω) := by sorry
