-- Prove2me | Theorems.Thm_LefebvreVariations_hadamard_exists_order_116
-- name    : LefebvreVariations.hadamard_exists_order_116
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:08:58.403265+00:00
-- url     : https://prove2.me/theorems/1c1e420a-f214-59a5-a9f7-537cdfc89329
-- title:
--   Lefebvre's variations, No. 71 — on a theme by Hadamard: a Hadamard matrix of order 116 exists
-- statement:
--   There is a $116\times116$ matrix $M$ with all entries $\pm1$ attaining Hadamard's determinant bound:
--   $$
--   |\det M| \;=\; 116^{116/2}.
--   $$
--
--   Equivalently, there is a Hadamard matrix of order $116=4\cdot 29$. This is one case of the Hadamard conjecture ($4k\times 4k$ Hadamard matrices exist for every $k$). The order $116$ is not a Paley order ($115$ is not a prime power, and $116=2(q+1)$ would need $q=57$), so it needs a different construction; one is provided by Williamson's method, which uses four symmetric circulant $\pm1$ matrices of order $29$.
--
--   **Formalization Note** The statement is the platform's determinant form of the Hadamard conjecture, `Hadamard_Conjecture`, with the index $k=29$: a real matrix indexed by `Fin (4 * 29)` with every entry in $\{1,-1\}$ and `|M.det| = (116 : ℝ) ^ ((116 : ℝ) / 2)`, with the real power written as in the parent.
--
--   **Why this is a variation.** Variation on the open mission 'The Hadamard Conjecture' (Hadamard_Conjecture). It is the case k = 29, stated with the parent's own determinant formulation: the first order past the Paley and Sylvester families that needs a Williamson-type construction. An explicit 116x116 sign matrix (or four circulant blocks of order 29) is a finite certificate, a model for attacking the next unsettled orders.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   H. Hadamard, Resolution d'une question relative aux determinants, Bull. Sci. Math. 17 (1893) 240-246 (the determinant bound). J. Williamson, Hadamard's determinant theorem and the sum of four squares, Duke Math. J. 11 (1944) 65-81 (Williamson matrices and the array; existence of Williamson matrices of order 29 cited from memory). Truth check: the author found four symmetric circulant +-1 matrices A,B,C,D of order 29 with A^2+B^2+C^2+D^2 = 116 I by a computer search and verified that the Williamson array built from them is a 116x116 +-1 matrix H with H H^T = 116 I, hence |det H| = 116^58. Origin of this statement: the open mission 'The Hadamard Conjecture' (theorem Hadamard_Conjecture), specialised to k = 29.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- A Hadamard matrix of order `116 = 4 * 29` exists, in the determinant form of the Hadamard conjecture. -/
theorem hadamard_exists_order_116 :
    ∃ M : Matrix (Fin (4 * 29)) (Fin (4 * 29)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * 29 : ℕ) : ℝ) ^ (((4 * 29 : ℕ) : ℝ) / 2) := by
  sorry

end LefebvreVariations
