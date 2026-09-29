-- Prove2me | Theorems.Thm_Hadamard_Conjecture
-- name    : Hadamard_Conjecture
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-06-25T18:45:36.792256+00:00
-- url     : https://prove2.me/theorems/4b4c7dbe-ff60-4d36-bc85-a46c9a1933a2
-- statement:
--   **Hadamard conjecture.** For every $k$ there exists a $4k\times4k$ matrix with $\pm1$ entries attaining Hadamard's determinant bound $|\det M| = (4k)^{4k/2}$ — equivalently, a Hadamard matrix of order $4k$. (Determinant form, following the DeepMind formal-conjectures library.)
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Hadamard.lean

import Mathlib

theorem Hadamard_Conjecture (k : ℕ) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
