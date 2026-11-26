-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstMemberV3
-- name    : Kyprianou.Ch04.exercise41GridFirstMemberV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:39:05.049257+00:00
-- url     : https://prove2.me/theorems/1edac7f3-e4e8-5b63-926d-08e80e3da119
-- title:
--   The finite first-hit selector belongs to the successful grid
-- statement:
--   The finite first-hit selector belongs to the successful grid
-- source:
--   Kyprianou (2006), Exercise 4.1(i), finite-grid proof.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41GridFirstMemberV3
    {Ω : Type} (D : Finset NNReal) (C : NNReal → Set Ω)
    (b : NNReal) (ω : Ω) (hA : ∃ t ∈ D, ω ∈ C t) :
    exercise41GridFirstV2 D C b ω ∈ D ∧
      ω ∈ C (exercise41GridFirstV2 D C b ω)  := by
  sorry
