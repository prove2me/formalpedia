-- Prove2me | Theorems.Thm_LefebvreVariations_hadamard_exists_order_92
-- name    : LefebvreVariations.hadamard_exists_order_92
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:35:50.24814+00:00
-- url     : https://prove2.me/theorems/847c9aca-9256-4949-9d49-c115a2a32606
-- title:
--   Lefebvre's variations, No. 24 — on a theme by Hadamard: a Hadamard matrix of order 92
-- statement:
--   This is the Hadamard conjecture at order $92$.
--
--   There is a $92\times92$ matrix $H$ with all entries in $\{1,-1\}$ and pairwise orthogonal rows:
--
--   $$
--   HH^{\mathsf T}=92\,I_{92}.
--   $$
--
--   The Hadamard conjecture asserts that such a matrix exists for every order divisible by $4$. Sylvester's doubling and Paley's constructions over finite fields cover most small orders, and $92=4\cdot23$ is the smallest order $4k$ with $k$ odd that they miss; it was settled by Baumert, Golomb and Hall with Williamson's construction, using four symmetric $\pm1$ sequences of length $23$ whose periodic autocorrelations sum to zero at every nonzero shift.
--
--   **Formalization Note** The statement is the parent's orthogonality form at order $92$, with entries in the finite set $\{1,-1\}$ of reals.
-- source:
--   L. Baumert, S. W. Golomb and M. Hall Jr., Discovery of an Hadamard matrix of order 92, Bull. Amer. Math. Soc. 68 (1962), 237–238; construction: J. Williamson, Hadamard's determinant theorem and the sum of four squares, Duke Math. J. 11 (1944), 65–81. Parent problem: Hadamard.exists_orthogonal_pm_one (Hadamard conjecture).

import Mathlib

set_option autoImplicit false

open Matrix

namespace LefebvreVariations

/-- **A Hadamard matrix of order 92 = 4·23**, the first order `4k` (`k = 23` odd) not reached by
Sylvester doubling or either Paley construction. Baumert–Golomb–Hall, "Discovery of an Hadamard
matrix of order 92", *Bull. Amer. Math. Soc.* 68 (1962) 237–238, via Williamson's construction
(Duke Math. J. 11 (1944) 65–81) with four symmetric `±1` circulants of order 23. -/
theorem hadamard_exists_order_92 :
    ∃ M : Matrix (Fin (4 * 23)) (Fin (4 * 23)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      M * Mᵀ = ((4 * 23 : ℕ) : ℝ) • (1 : Matrix (Fin (4 * 23)) (Fin (4 * 23)) ℝ) := by
  sorry

end LefebvreVariations
