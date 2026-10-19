-- Prove2me | Theorems.Thm_Hadamard_Conjecture_nonpoweroftwo
-- name    : Hadamard_Conjecture_nonpoweroftwo
-- status  : Open
-- author  : @ronr
-- created : 2026-09-05T16:49:50.182533+00:00
-- url     : https://prove2.me/theorems/d44ed3f8-d154-42b6-a6f6-e4e89abcea74
-- title:
--   Hadamard conjecture, residual non-power-of-two case
-- statement:
--   This is the residual case of the Hadamard conjecture left open after removing the classical Sylvester family.
--
--   For a natural number $k$ that is **not** a power of two (there is no $m$ with $k = 2^m$), the claim is that there exists a $4k \times 4k$ matrix $M$ with every entry equal to $1$ or $-1$ and attaining Hadamard's determinant bound:
--
--   $$
--   |\det M| = (4k)^{4k/2}.
--   $$
--
--   This is exactly the statement `Hadamard_Conjecture` for $k$ restricted to the case where $4k$ is not a power of two times $4$ in the classical sense covered by Sylvester's 1867 doubling construction ($k = 2^m$, giving order $2^{m+2}$). Sylvester's construction settles the conjecture unconditionally whenever $k$ is a power of two; for every other $k$ (e.g. $k = 3, 5, 6, 7, 9, \ldots$), existence of a Hadamard matrix of order $4k$ is known only case by case (Paley, Williamson, and many other constructions cover most small and many large orders, and no counterexample is known), and no proof covering every remaining $k$ is known. This restricted statement is therefore exactly as open as the general Hadamard conjecture, minus the powers-of-two case.
--
--   **Formalization Note** Matrix entries live in $\mathbb{R}$; membership in $\{1,-1\}$ is expressed as `Finset` membership. The determinant exponent $4k/2$ is a real number via `Real.rpow`; since $4k$ is always even this equals the natural number $2k$, but the statement keeps the same real-exponent form as `Hadamard_Conjecture` for direct compatibility.
-- source:
--   Residual case derived from the classical Hadamard conjecture (J. Hadamard, 1893, Resolution d'une question relative aux determinants, Bull. Sci. Math. 17, 240-246) after removing the case k = 2^m, which is fully settled by Sylvester's 1867 construction (J. J. Sylvester, Thoughts on inverse orthogonal matrices, Philos. Mag. 34, 461-475). Formal target statement follows the DeepMind formal-conjectures library's determinant form: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Hadamard.lean. This restriction to non-power-of-two k is original to this Prove2Me submission, derived as the child of a proof-sketch reduction of Hadamard_Conjecture (theorem_id 4b4c7dbe-ff60-4d36-bc85-a46c9a1933a2) that proves the k = 2^m case directly via Sylvester's construction.

import Mathlib

theorem Hadamard_Conjecture_nonpoweroftwo (k : ℕ) (hk : ¬ ∃ m : ℕ, k = 2 ^ m) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
