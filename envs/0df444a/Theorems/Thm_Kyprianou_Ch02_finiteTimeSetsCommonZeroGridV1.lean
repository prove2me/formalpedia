-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteTimeSetsCommonZeroGridV1
-- name    : Kyprianou.Ch02.finiteTimeSetsCommonZeroGridV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:22:08.247316+00:00
-- url     : https://prove2.me/theorems/bda1c94f-3d7e-44c1-82d9-c3e9e7cd6df6
-- title:
--   Two finite time sets admit a common monotone grid starting at zero
-- statement:
--   Two finite time sets admit a common monotone grid starting at zero
-- source:
--   Kyprianou (2006), Exercise 2.8, finite-grid independence argument.

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteTimeSetsCommonZeroGridV1
    (I J : Finset ℝ≥0) :
    ∃ (n : ℕ) (t : Fin (n+1) → ℝ≥0), Monotone t ∧ t 0 = 0 ∧
      (∀ i : I, ∃ k, t k = i) ∧ (∀ j : J, ∃ k, t k = j) := by sorry
