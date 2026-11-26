-- Prove2me | Theorems.Thm_LefebvreVariations_hadamard_exists_order_188
-- name    : LefebvreVariations.hadamard_exists_order_188
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:09:55.422289+00:00
-- url     : https://prove2.me/theorems/a8e15594-2b48-42a1-b794-b03bdbcbd858
-- title:
--   Lefebvre's variations, No. 127 — on a theme by Hadamard: a Hadamard matrix of order 188 exists
-- statement:
--   There is a $\{\pm1\}$-matrix $M$ of size $4\cdot 47=188$ with
--   $$|\det M| = 188^{188/2}.$$
--
--   Equivalently (Hadamard 1893), $M$ is a Hadamard matrix of order $188$: $MM^{T}=188I$. The order $188=4\cdot47$ is not reached by the Sylvester and Paley constructions (neither $188$ is a power of 2 nor of the form $(q+1)2^t$ with $q\equiv3 \bmod 4$ prime, nor $2(q+1)2^t$ with $q \equiv 1 \bmod 4$ prime power), so it lies in the residual range of the Hadamard conjecture. Hadamard matrices are known for every order $4k<668$.
--
--   **Formalization Note** The statement is the platform's `Hadamard_Conjecture` with `k = 47`: a real matrix indexed by `Fin (4 * 47)` whose entries lie in `{1, -1}` and whose absolute determinant equals `188^(188/2)` (real power).
--
--   **Why this is a variation.** Variation on the open Hadamard_Conjecture (and its residual cases after Sylvester and Paley). It is the case k = 47, an order outside the Sylvester and Paley families, stated with the parent's own determinant formulation and unchanged conclusion; known to be true in the literature, and an explicit certificate is a finite check for a prover.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Hadamard matrices of every order 4k < 668 are known; the smallest open order is 668 (H. Kharaghani and B. Tayfeh-Rezaie, A Hadamard matrix of order 428, J. Combin. Designs 13 (2005) 435-440, which settled the previous smallest open case; the all-orders-below-668 statement is as reported on https://en.wikipedia.org/wiki/Hadamard_matrix and in the Hadamard matrix literature, verified by web search, but the specific construction for order 188 was not looked up). Sloane's library of Hadamard matrices (neilsloane.com/hadamard) lists matrices of these orders (not re-checked). Hadamard's determinant bound: J. Hadamard, Bull. Sci. Math. 17 (1893) 240-246 (cited from memory). Origin: platform theorem Hadamard_Conjecture, case k = 47.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- A Hadamard matrix of order `188 = 4 * 47` exists, in the determinant form of the Hadamard conjecture. -/
theorem hadamard_exists_order_188 :
    ∃ M : Matrix (Fin (4 * 47)) (Fin (4 * 47)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * 47 : ℕ) : ℝ) ^ (((4 * 47 : ℕ) : ℝ) / 2) := by
  sorry

end LefebvreVariations
