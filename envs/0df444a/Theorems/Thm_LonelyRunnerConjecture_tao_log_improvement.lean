-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_tao_log_improvement
-- name    : LonelyRunnerConjecture.tao_log_improvement
-- status  : Open
-- author  : @LG
-- created : 2026-11-17T01:13:24.226203+00:00
-- url     : https://prove2.me/theorems/3d69f81e-bd1c-4e58-b3b0-4e123a54f95d
-- title:
--   Tao's logarithmic improvement of the union bound
-- statement:
--   There is an absolute constant $c>0$ and a threshold $N$ such that for all $k\ge N$ and any $k$ distinct positive integer speeds, some time $t$ satisfies $\|tv\|\ge \frac{1}{2k}+\frac{c\log k}{k^2(\log\log k)^2}$ for every speed. This is the best known asymptotic lower bound on the gap of loneliness.
--
--   **Formalization Note** "Sufficiently large" is `∃ N, ∀ k ≥ N`; logarithms are `Real.log`.
-- source:
--   T. Tao, Some remarks on the lonely runner conjecture, https://arxiv.org/abs/1701.02048 (v4), Theorem 1.2.

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem tao_log_improvement :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ S : Finset ℕ, S.card = k → (∀ v ∈ S, 0 < v) →
        ∃ t : ℝ, ∀ v ∈ S,
          (1 : ℝ) / (2 * k : ℝ)
            + c * Real.log (k : ℝ) / ((k : ℝ) ^ 2 * (Real.log (Real.log (k : ℝ))) ^ 2)
          ≤ distToNearestInt (t * (v : ℝ)) := by sorry

end LonelyRunnerConjecture
