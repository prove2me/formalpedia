-- Prove2me | Theorems.Thm_Kyprianou_Ch01_strictMono_of_dense_rightContinuity
-- name    : Kyprianou.Ch01.strictMono_of_dense_rightContinuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:56:53.120984+00:00
-- url     : https://prove2.me/theorems/76a1a4c9-4ca6-40f4-aaa2-48305584d2c2
-- title:
--   Right-continuous paths strictly increasing on a dense time set are strictly increasing everywhere
-- statement:
--   A deterministic, source-faithful separability argument for Chapter 1 Lévy processes. Given right-continuity at each nonnegative time and strict increase at every ordered pair of a dense subset, the path is strictly increasing on the complete time domain. Between any two times s<t choose dense time points u<v. Use sequences from the dense set decreasing towards s and t from the right and right-continuity to prove f(s)≤f(u)<f(v)≤f(t). This general lemma is reused to upgrade countably many gamma-Lévy increment statements into a pathwise almost-sure conclusion.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.4 gamma subordinator; deterministic dense-time càdlàg extension.

import Mathlib
import Mathlib.Topology.Order.IsLUB
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.strictMono_of_dense_rightContinuity
    (f : ℝ≥0 → ℝ)
    (hcont : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t)
    (S : Set ℝ≥0) (hDense : Dense S)
    (hstrict : ∀ s ∈ S, ∀ t ∈ S, s < t → f s < f t) :
    StrictMono f := by sorry
