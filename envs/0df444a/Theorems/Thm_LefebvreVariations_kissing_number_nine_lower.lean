-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_nine_lower
-- name    : LefebvreVariations.kissing_number_nine_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:13:37.323057+00:00
-- url     : https://prove2.me/theorems/cf88732d-211d-403e-b2fb-79a0c1682e43
-- title:
--   Lefebvre's variations, No. 89 — on a theme by Conway and Sloane: the kissing number in dimension 9 is at least 306
-- statement:
--   Let $\tau(9)$ be the kissing number in dimension $9$: the largest size of a finite set of unit vectors in $\mathbb{R}^{9}$ with pairwise inner products at most $\tfrac12$. Then
--   $$
--   \tau(9) \;\ge\; 306.
--   $$
--
--   An explicit configuration: take the $2\cdot9$ vectors $\pm 2e_i$ together with, for each of 18 four-element subsets $S$ of $\{1,\dots,9\}$ chosen so that any two of them share at most two points, the $16$ vectors that are $\pm1$ on $S$ and $0$ elsewhere; all have squared norm $4$ and pairwise inner products at most $2$, so after rescaling by $\tfrac12$ they are $2\cdot9+16\cdot 18=306$ unit vectors with pairwise inner products at most $\tfrac12$. (This is Construction A applied to a binary constant-weight code of length $9$, distance $4$, size $18$.) The exact value of $\tau(9)$ is not known.
--
--   **Formalization Note** The kissing number is the platform's `KissingNumber.kissingNumber 9 : ℕ∞`, the supremum, over all `KissingConfig 9` (a `Finset` of vectors of `EuclideanSpace ℝ (Fin 9)` of norm exactly $1$ with pairwise real inner product at most $1/2$ between distinct members), of the cardinality. The statement is `(306 : ℕ∞) ≤ kissingNumber 9`; no upper bound is asserted.
--
--   **Why this is a variation.** Variation on the open mission 'The Kissing Number Problem' (parent theorems KissingNumber.kissing_number_three, _four, _five, _eight, _twentyfour). It is the lower half of the determination of tau(9), stated with the parent's own KissingNumber definitions, a partial result with an explicit finite configuration of 306 points; improving it or matching an upper bound is exactly the open problem in this dimension.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999: Construction A and the non-lattice packing P9a in dimension 9, kissing number 306 (Chapter 5 and the table of kissing numbers in Chapter 1; section and table numbers cited from memory). Truth check: the author built the 306 vectors described above from 18 four-element subsets of a 9-point set pairwise meeting in at most two points (found by computer search) and verified by computer that they are 306 distinct vectors of squared norm 4 with all pairwise inner products at most 2. Larger kissing configurations in dimension 9 may be known; only the lower bound 306 is asserted. Origin: the open mission 'The Kissing Number Problem'.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations

open KissingNumber

/-- Lower bound for the kissing number in dimension 9: `306 ≤ τ(9)`, by an explicit configuration. -/
theorem kissing_number_nine_lower : (306 : ℕ∞) ≤ kissingNumber 9 := by
  sorry

end LefebvreVariations
