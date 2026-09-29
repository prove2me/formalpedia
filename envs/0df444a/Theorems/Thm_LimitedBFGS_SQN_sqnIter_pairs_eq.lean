-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_sqnIter_pairs_eq
-- name    : LimitedBFGS.SQN.sqnIter_pairs_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T21:10:13.256109+00:00
-- url     : https://prove2.me/theorems/fd1881e3-01a3-4835-b267-f14f8447a23a
-- title:
--   The SQN iteration retains exactly the PCG pair window
-- statement:
--   Fix `m ≥ 1`. The SQN iteration stores at most `m` correction pairs, oldest first, and `pcgPairs A b H₀ x₀ m k` is the same window built from the PCG iterates.
--
--   **Claim.** If the SQN and PCG iterates agree at every index `j ≤ k`, then the retained pair lists agree at `k`.
--
--   **Why.** Both lists start empty at index `0`, and each successor appends the pair `(x_{j+1} - x_j, g_{j+1} - g_j)` computed at step `j` and then drops entries beyond `m`. Under the hypothesis the appended pairs coincide term by term, so the two lists coincide at every index.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, iteration (17).

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix

namespace LimitedBFGS.SQN

/-- The window of pairs retained by the SQN iteration (17) after `k` steps is, once the
iterates agree, exactly the window `pcgPairs A b H₀ x₀ m k` of PCG pairs: both start empty,
append the newest pair, and drop the oldest entries past `m`. -/
theorem sqnIter_pairs_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (x₀ : Fin n → ℝ) (k : ℕ)
    (hx : ∀ j ≤ k, (sqnIter A b H₀ m x₀ j).x = (pcgIter A b H₀ x₀ j).x) :
    (sqnIter A b H₀ m x₀ k).pairs = pcgPairs A b H₀ x₀ m k := by sorry

end LimitedBFGS.SQN
