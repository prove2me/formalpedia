-- Prove2me | Theorems.Thm_Kyprianou_Ch01_rationalUpperCrossingBeforeAnyLaterTimePublic
-- name    : Kyprianou.Ch01.rationalUpperCrossingBeforeAnyLaterTimePublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:41:08.931697+00:00
-- url     : https://prove2.me/theorems/2ffe17e6-81fe-4419-8c02-43a05cff27f8
-- title:
--   Any later time after a continuous upper passage contains a rational strict crossing
-- statement:
--   For any continuous real path, if its first strictly positive upper passage occurs before a finite time t, a positive rational observation strictly before t already exceeds the barrier. Rational approaching crossings with ε=t minus the first-passage infimum give such a time.
-- source:
--   Kyprianou (2006) Exercise 1.10(ii), rational approximation of continuous first passage.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.rationalUpperCrossingBeforeAnyLaterTimePublic
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω))
    (t : ℝ≥0)
    (ht : firstUpperPassage X s ω < (t : WithTop ℝ≥0)) :
    ∃ r : ℚ, 0 < (r : ℝ) ∧
      Real.toNNReal (r : ℝ) < t ∧
      s < X (Real.toNNReal (r : ℝ)) ω := by sorry
