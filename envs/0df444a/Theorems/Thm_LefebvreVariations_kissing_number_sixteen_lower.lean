-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_sixteen_lower
-- name    : LefebvreVariations.kissing_number_sixteen_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:14:36.659396+00:00
-- url     : https://prove2.me/theorems/b25eab3b-1ea2-5b19-bc3d-3e73351048ab
-- title:
--   Lefebvre's variations, No. 91 — on a theme by Conway and Sloane: the kissing number in dimension 16 is at least 4320
-- statement:
--   Let $\tau(16)$ be the kissing number in dimension $16$: the largest size of a finite set of unit vectors in $\mathbb{R}^{16}$ with pairwise inner products at most $\tfrac12$. Then
--   $$
--   \tau(16) \;\ge\; 4320.
--   $$
--
--   The bound is attained by the $4320$ minimal vectors of the Barnes-Wall lattice $\Lambda_{16}$, rescaled to unit length. In coordinates (squared norm $8$): the $480$ vectors with two coordinates $\pm2$ and fourteen zeros, and the $3840$ vectors that are $\pm1$ on the $8$-element support of one of the $30$ codewords of weight $8$ of the first-order Reed-Muller code $RM(1,4)$ with an even number of minus signs, and $0$ elsewhere. Their pairwise inner products are at most $4$, i.e. at most $\tfrac12$ after rescaling. The exact value of $\tau(16)$ is not known.
--
--   **Formalization Note** The kissing number is the platform's `KissingNumber.kissingNumber 16 : ℕ∞`, the supremum, over all `KissingConfig 16` (a `Finset` of vectors of `EuclideanSpace ℝ (Fin 16)` of norm exactly $1$ with pairwise real inner product at most $1/2$ between distinct members), of the cardinality. The statement is `(4320 : ℕ∞) ≤ kissingNumber 16`; no upper bound is asserted.
--
--   **Why this is a variation.** Variation on the open mission 'The Kissing Number Problem' (parent theorems KissingNumber.kissing_number_three, _four, _five, _eight, _twentyfour). It is the lower half of the determination of tau(16), the first dimension where the Barnes-Wall lattice gives the best known configuration, stated with the parent's own KissingNumber definitions. The explicit 4320 points are a finite certificate, and any improvement or matching upper bound settles the open question in this dimension.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999: the Barnes-Wall lattice Lambda_16 and its 4320 minimal vectors (Chapter 4 and the table of kissing numbers in Chapter 1; chapter and table numbers cited from memory). E. S. Barnes and G. E. Wall, Some extreme forms defined in terms of Abelian groups, J. Austral. Math. Soc. 1 (1959) 47-63 (cited from memory). Truth check: the author generated the 4320 vectors described above and verified by computer that they are distinct, all of squared norm 8, with every pairwise inner product at most 4. The best known lower bound in dimension 16 is 4320 (cited from memory); the exact value is open. Origin: the open mission 'The Kissing Number Problem'.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations

open KissingNumber

/-- Lower bound for the kissing number in dimension 16: `4320 ≤ τ(16)`, by an explicit configuration. -/
theorem kissing_number_sixteen_lower : (4320 : ℕ∞) ≤ kissingNumber 16 := by
  sorry

end LefebvreVariations
