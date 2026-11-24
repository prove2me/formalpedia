-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyGridLaplaceDeficitV1
-- name    : Kyprianou.Ch02.levyGridLaplaceDeficitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:18:45.327222+00:00
-- url     : https://prove2.me/theorems/de90afd7-dc66-4981-9dba-653485974f45
-- title:
--   Uniform power lower bound controls scaled deficits
-- statement:
--   Positivity of the powers ensures q is positive. Take logarithms and use log q ≤ q-1.
-- source:
--   Kyprianou (2006), Lemma 2.12

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyGridLaplaceDeficitV1
    (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c ≤ q n ^ (n+1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ((n : ℝ)+1)*(1-q n) ≤ C := by sorry
