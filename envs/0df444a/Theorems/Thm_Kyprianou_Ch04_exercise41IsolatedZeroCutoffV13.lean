-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41IsolatedZeroCutoffV13
-- name    : Kyprianou.Ch04.exercise41IsolatedZeroCutoffV13
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:56:45.231021+00:00
-- url     : https://prove2.me/theorems/3684eb74-f99d-572e-9a2c-8d9a677c3d0d
-- title:
--   Dense cutoff before a locally isolated positive zero
-- statement:
--   Dense cutoff before a locally isolated positive zero
-- source:
--   Kyprianou (2006), Exercise 4.1(ii) auxiliary result

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41IsolatedZeroCutoffV13
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (s : NNReal) (hs : 0 < s)
    (hf : Set.Finite {u : NNReal | 0 < u ∧ u ≤ s ∧ x u = 0}) :
    ∃ j : ℕ, 0 < q j ∧ q j < s ∧ ∀ u ∈ Ico (q j) s, x u ≠ 0 := by
  sorry
