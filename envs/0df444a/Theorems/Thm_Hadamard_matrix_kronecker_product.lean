-- Prove2me | Theorems.Thm_Hadamard_matrix_kronecker_product
-- name    : Hadamard_matrix_kronecker_product
-- status  : Proved
-- author  : @ronr
-- created : 2026-09-05T19:53:34.852834+00:00
-- url     : https://prove2.me/theorems/635fbe02-d442-43c6-b1a0-b7dff65843e0
-- title:
--   Kronecker product of Hadamard matrices
-- statement:
--   This is the classical multiplicativity theorem for Hadamard matrices: the Kronecker (tensor) product of two Hadamard matrices is again a Hadamard matrix, of order equal to the product of the two orders.
--
--   Let $A$ be an $m\times m$ real matrix with every entry $1$ or $-1$ satisfying $AA^{\mathsf T}=mI_m$, and let $B$ be an $n\times n$ real matrix with every entry $1$ or $-1$ satisfying $BB^{\mathsf T}=nI_n$ (i.e. $A$ and $B$ are each Hadamard matrices in orthogonality form). Then the Kronecker product $A\otimes B$, an $mn\times mn$ matrix, has every entry $1$ or $-1$ and satisfies
--
--   $$
--   (A\otimes B)(A\otimes B)^{\mathsf T} = mn\, I_{mn}.
--   $$
--
--   The proof uses the mixed-product identity $(A\otimes B)(C\otimes D)=(AC)\otimes(BD)$: every entry of $A\otimes B$ is a product of a $\pm1$ entry of $A$ and a $\pm1$ entry of $B$, hence $\pm1$, and
--
--   $$
--   (A\otimes B)(A\otimes B)^{\mathsf T}=(AA^{\mathsf T})\otimes(BB^{\mathsf T})=(mI_m)\otimes(nI_n)=mn\,I_{mn}.
--   $$
--
--   This generalizes Sylvester's 1867 doubling construction (the case $B$ is the fixed $2\times2$ matrix $\begin{pmatrix}1&1\\1&-1\end{pmatrix}$) to the tensor product of any two Hadamard matrices, and is the standard tool for multiplying together the orders of known Hadamard matrices: if Hadamard matrices of orders $m$ and $n$ exist, so does one of order $mn$.
--
--   **Formalization Note** Both hypotheses and the conclusion are stated in orthogonality form ($MM^{\mathsf T}=NI_N$) rather than the determinant form, matching the internal representation used to build Sylvester's construction on this platform. The index type of the product matrix is `Fin (m * n)`, reached from the natural Kronecker index type `Fin m × Fin n` via the standard equivalence `finProdFinEquiv`.
-- source:
--   Classical multiplicativity/Kronecker-product theorem for Hadamard matrices, generalizing J. J. Sylvester, Thoughts on inverse orthogonal matrices, simultaneous sign successions, and tessellated pavements in two or more colours, Philos. Mag. 34 (1867), 461-475 (the fixed-order-2 case of the tensor step) to arbitrary Hadamard matrix factors. Standard textbook result; see e.g. K. J. Horadam, Hadamard Matrices and Their Applications, Princeton University Press, 2007, Section 1.2 (multiplication theorem via Kronecker products).

import Mathlib
open Matrix

theorem Hadamard_matrix_kronecker_product {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hApm : ∀ i j, A i j = 1 ∨ A i j = -1)
    (hAorth : A * Aᵀ = ((m : ℕ) : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ))
    (hBpm : ∀ i j, B i j = 1 ∨ B i j = -1)
    (hBorth : B * Bᵀ = ((n : ℕ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ M : Matrix (Fin (m * n)) (Fin (m * n)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((m * n : ℕ) : ℝ) • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) := by sorry
