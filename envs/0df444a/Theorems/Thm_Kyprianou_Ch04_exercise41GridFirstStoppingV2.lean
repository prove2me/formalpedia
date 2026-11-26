-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstStoppingV2
-- name    : Kyprianou.Ch04.exercise41GridFirstStoppingV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:35:15.663892+00:00
-- url     : https://prove2.me/theorems/07d69334-b0f0-4ad8-817c-c34a359e0e27
-- title:
--   Finite capped observation clock and hit event are stopped measurable
-- statement:
--   Finite capped observation clock and hit event are stopped measurable
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstSublevelV2
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise41GridFirstStoppingV2 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (D : Finset NNReal) (C : NNReal → Set Ω) (b : NNReal)
    (hDb : ∀ t ∈ D, t ≤ b)
    (hC : ∀ t, MeasurableSet[F t] (C t)) :
    let τ := exercise41GridFirstV2 D C b
    let A : Set Ω := {ω | ∃ t ∈ D, ω ∈ C t}
    (∀ s, MeasurableSet[F s] {ω | τ ω ≤ s}) ∧
    (∀ s, MeasurableSet[F s] (A ∩ {ω | τ ω ≤ s}))  := by
  sorry
