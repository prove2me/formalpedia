-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcgPair_s_eq
-- name    : LimitedBFGS.SQN.pcgPair_s_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T21:09:44.418952+00:00
-- url     : https://prove2.me/theorems/7b58b19a-e9ce-49af-97ed-a7161807e042
-- title:
--   The stored step of a PCG pair is the line-search step times the search direction
-- statement:
--   Let `pcgPair A b H₀ x₀ k = (s_k, y_k)` be the secant pair stored after the step from `x_k`.
--
--   **Claim.** `s_k = exactStep A b x_k d_k • d_k`.
--
--   **Why.** By the definition of `pcgIter`, the successor iterate is `x_{k+1} = x_k + exactStep A b x_k d_k • d_k`, and `s_k = x_{k+1} - x_k`.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 777-778, iteration (13).

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix

namespace LimitedBFGS.SQN

/-- The first component of `pcgPair A b H₀ x₀ k` is the line-search step `α_k` times the
direction `d_k`, because `pcgIter` moves the iterate by `exactStep … • d`. -/
theorem pcgPair_s_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    (pcgPair A b H₀ x₀ k).1
      = exactStep A b (pcgIter A b H₀ x₀ k).x (pcgIter A b H₀ x₀ k).d
          • (pcgIter A b H₀ x₀ k).d := by sorry

end LimitedBFGS.SQN
