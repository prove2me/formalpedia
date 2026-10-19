-- Prove2me | Theorems.Thm_Hadamard_Conjecture_paley_sylvester_case
-- name    : Hadamard_Conjecture_paley_sylvester_case
-- status  : Proved
-- author  : @ronr
-- created : 2026-09-05T22:12:32.640886+00:00
-- url     : https://prove2.me/theorems/f34b2765-011b-466c-995d-499ee3c8daa6
-- title:
--   Hadamard conjecture: the Paley-times-power-of-two case
-- statement:
--   This is the case of the Hadamard conjecture reachable by combining Paley's construction with Sylvester's doubling construction via the Kronecker-product multiplicativity theorem.
--
--   Suppose $k$ is a natural number for which there exist a prime $q \equiv 3 \pmod 4$ and a natural number $t$ with
--
--   $$
--   4k = (q+1) \cdot 2^{t}.
--   $$
--
--   Then there exists a $4k \times 4k$ matrix $M$ with every entry $1$ or $-1$ attaining Hadamard's determinant bound $|\det M| = (4k)^{4k/2}$.
--
--   **Proof idea.** Paley's construction (`Paley_construction_I`, applied to the finite field $\mathbb Z/q\mathbb Z$) gives a Hadamard matrix of order $q+1$; Sylvester's doubling construction gives one of order $2^{t}$. The Kronecker-product multiplicativity theorem (`Hadamard_matrix_kronecker_product`) combines them into one of order $(q+1)\cdot 2^{t} = 4k$.
--
--   This theorem, together with the case $k = 2^m$ (settled unconditionally by Sylvester's construction alone in the `Hadamard_Conjecture` proof-sketch) and a further residual case, is intended as one branch of a finer case split refining `Hadamard_Conjecture_nonpoweroftwo`; it does not by itself close the Hadamard conjecture, since infinitely many $k$ satisfy neither hypothesis (e.g. $k$ for which $4k$ has no divisor of the form $q+1$ with $q$ prime, $q \equiv 3 \pmod 4$).
--
--   **Formalization Note** Since every Hadamard matrix of order $4k$ has an underlying orthogonality identity $MM^{\mathsf T} = 4kI_{4k}$, the determinant bound $|\det M| = (4k)^{4k/2}$ follows from $(\det M)^2 = \det(MM^{\mathsf T}) = (4k)^{4k}$ and evenness of $4k$; this conversion is internal to the proof and not part of the statement.
-- source:
--   Combination of R. E. A. C. Paley, On orthogonal matrices, Journal of Mathematics and Physics 12 (1933), 311-320, with J. J. Sylvester's 1867 doubling construction (Philos. Mag. 34, 461-475), via the classical Kronecker-product multiplicativity theorem for Hadamard matrices. Built on Prove2Me theorems Paley_construction_I (65d083bb-43e4-4dfd-a728-69945984f8e0) and Hadamard_matrix_kronecker_product (635fbe02-d442-43c6-b1a0-b7dff65843e0), and derived as a further reduction of Hadamard_Conjecture_nonpoweroftwo (d44ed3f8-d154-42b6-a6f6-e4e89abcea74).

import Mathlib
open Matrix

theorem Hadamard_Conjecture_paley_sylvester_case (k : ℕ)
    (hk : ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 3 ∧ 4 * k = (q + 1) * 2 ^ t) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
