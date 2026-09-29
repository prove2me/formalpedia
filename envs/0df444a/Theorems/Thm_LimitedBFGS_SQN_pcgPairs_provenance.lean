-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcgPairs_provenance
-- name    : LimitedBFGS.SQN.pcgPairs_provenance
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T21:09:20.897926+00:00
-- url     : https://prove2.me/theorems/b8a49295-44a9-4ae6-97d5-e934c839521c
-- title:
--   Every pair retained by the limited-storage PCG window was created at an earlier step
-- statement:
--   Let `pcgPairs A b H₀ x₀ m k` be the list of the most recent `m` PCG correction pairs retained after `k` steps, oldest first.
--
--   **Claim.** Every pair `p` in that list equals `pcgPair A b H₀ x₀ j` for some `j < k`.
--
--   **Why.** The list starts empty at `k = 0`. At a successor step the new pair `pcgPair … k` is appended and the oldest entries are dropped, so nothing later than index `k` ever enters. Dropping can only remove elements, never add them.
-- source:
--   Nocedal, Updating Quasi-Newton Matrices with Limited Storage, Math. Comp. 35 (1980), p. 778, iteration (17).

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgPairs
import Definitions.Def_LimitedBFGS_SQN_sqnIter

open Matrix

namespace LimitedBFGS.SQN

/-- Provenance for the window `pcgPairs A b H₀ x₀ m k`. Every pair still stored after `k`
steps is the pair `pcgPair A b H₀ x₀ j` created at some step `j < k`. This is all that is needed
to replay the fold: each retained pair is an old PCG secant pair, so the PCG orthogonality
relations apply to it. -/
theorem pcgPairs_provenance {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (m : ℕ) (k : ℕ) :
    ∀ p ∈ pcgPairs A b H₀ x₀ m k, ∃ j < k, p = pcgPair A b H₀ x₀ j := by sorry

end LimitedBFGS.SQN
