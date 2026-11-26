-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstSublevelV2
-- name    : Kyprianou.Ch04.exercise41GridFirstSublevelV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:32:39.820303+00:00
-- url     : https://prove2.me/theorems/20bb7fd7-c3c6-5f63-9941-c197d21804a6
-- title:
--   Finite first-hit sublevel equals finite union of observations
-- statement:
--   Finite first-hit sublevel equals finite union of observations
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41GridFirstSublevelV2 {Ω : Type}
    (D : Finset NNReal) (C : NNReal → Set Ω)
    (b s : NNReal) (ω : Ω) :
    ((∃ t ∈ D, ω ∈ C t) ∧ exercise41GridFirstV2 D C b ω ≤ s) ↔
      ∃ t ∈ D, ω ∈ C t ∧ t ≤ s  := by
  sorry
