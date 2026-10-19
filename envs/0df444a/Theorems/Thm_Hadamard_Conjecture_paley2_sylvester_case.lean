-- Prove2me | Theorems.Thm_Hadamard_Conjecture_paley2_sylvester_case
-- name    : Hadamard_Conjecture_paley2_sylvester_case
-- status  : Proved
-- author  : @ronr
-- created : 2026-09-06T00:01:29.671836+00:00
-- url     : https://prove2.me/theorems/9435d03e-376e-443f-aafb-4a4401eef530
-- title:
--   Hadamard conjecture: the Paley-II-times-power-of-two case
-- statement:
--   This is the case of the Hadamard conjecture reachable by combining Paley's second construction with Sylvester's doubling construction via the Kronecker-product multiplicativity theorem.
--
--   Suppose $k$ is a natural number for which there exist a prime $q \equiv 1 \pmod 4$ and a natural number $t$ with
--
--   $$
--   4k = 2(q+1) \cdot 2^{t}.
--   $$
--
--   Then there exists a $4k \times 4k$ matrix $M$ with every entry $1$ or $-1$ attaining Hadamard's determinant bound $|\det M| = (4k)^{4k/2}$.
--
--   **Proof idea.** Paley's second construction (`Paley_construction_II`, applied to the finite field $\mathbb Z/q\mathbb Z$) gives a Hadamard matrix of order $2(q+1)$; Sylvester's doubling construction gives one of order $2^{t}$. The Kronecker-product multiplicativity theorem (`Hadamard_matrix_kronecker_product`) combines them into one of order $2(q+1)\cdot2^{t} = 4k$.
--
--   This theorem is the Paley-II analogue of `Hadamard_Conjecture_paley_sylvester_case` (which uses Paley's *first* construction, $q\equiv3\pmod4$, order $q+1$). Together they cover further $k$ not reachable by either construction alone — for instance $q=5,13,17,29$ (each $\equiv1\pmod4$) give base orders $12,28,36,60$, i.e. $k=3,7,9,15$ and all their doublings.
--
--   As with the Paley-I case, this theorem is intended as one branch of a finer case split refining `Hadamard_Conjecture_residual`; it does not by itself close the Hadamard conjecture.
--
--   **Formalization Note** The determinant bound $|\det M|=(4k)^{4k/2}$ follows internally from the orthogonality identity $MM^{\mathsf T}=4kI_{4k}$ via $(\det M)^2=\det(MM^{\mathsf T})=(4k)^{4k}$ and evenness of $4k$.
-- source:
--   Combination of R. E. A. C. Paley, On orthogonal matrices, Journal of Mathematics and Physics 12 (1933), 311-320 (second construction, q = 1 mod 4), with J. J. Sylvester's 1867 doubling construction, via the classical Kronecker-product multiplicativity theorem for Hadamard matrices. Built on Prove2Me theorems Paley_construction_II (087846e2-e39f-4fe7-abfc-c09366c76aa9) and Hadamard_matrix_kronecker_product (635fbe02-d442-43c6-b1a0-b7dff65843e0), and derived as a further reduction of Hadamard_Conjecture_residual (cd4ba333-e7e7-4976-8259-f5cd3354c8ea), the Paley-II analogue of Hadamard_Conjecture_paley_sylvester_case (f34b2765-011b-466c-995d-499ee3c8daa6).

import Mathlib
open Matrix

theorem Hadamard_Conjecture_paley2_sylvester_case (k : ℕ)
    (hk : ∃ q t : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ 4 * k = (2 * (q + 1)) * 2 ^ t) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
