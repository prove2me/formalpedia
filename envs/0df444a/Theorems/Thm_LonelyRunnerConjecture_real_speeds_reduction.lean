-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_real_speeds_reduction
-- name    : LonelyRunnerConjecture.real_speeds_reduction
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-17T01:12:27.654004+00:00
-- url     : https://prove2.me/theorems/a30d709a-8356-4aa1-8add-5da03642d743
-- title:
--   Reduction from real to integer speeds
-- statement:
--   If the conjecture holds for $k$ positive integer speeds ($\mathrm{LRC}(k)$), then it holds for any $k$ distinct positive real speeds: there is a time $t$ with $\|t v_i\|\ge\frac{1}{k+1}$ for all $i$. This is the classical reduction justifying the restriction to integer speeds.
--
--   **Formalization Note** Real speeds are a function `Fin k → ℝ`, positive and injective; the integer case is the hypothesis `LRC k`.
-- source:
--   R. D. Malikiosis, F. Santos, M. Schymura, Linearly-exponential checking is enough for the LRC, https://arxiv.org/abs/2411.06903, §1.1 (reduction to integer velocities; Wills Lemma 5, Betke–Wills Lemma 1; Bohman–Holzman–Kleitman 2001; Henze–Malikiosis 2017).

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem real_speeds_reduction (k : ℕ) (h : LRC k) (v : Fin k → ℝ)
    (hpos : ∀ i, 0 < v i) (hinj : Function.Injective v) :
    ∃ t : ℝ, ∀ i, (1 : ℝ) / (k + 1 : ℝ) ≤ distToNearestInt (t * v i) := by sorry

end LonelyRunnerConjecture
