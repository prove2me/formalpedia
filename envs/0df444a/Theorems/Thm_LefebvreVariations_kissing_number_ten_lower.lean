-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_ten_lower
-- name    : LefebvreVariations.kissing_number_ten_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:14:13.303982+00:00
-- url     : https://prove2.me/theorems/838e648b-6afe-4a49-81bb-8c8e6ae8cb9c
-- title:
--   Lefebvre's variations, No. 79 — on a theme by Conway and Sloane: the kissing number in dimension 10 is at least 500
-- statement:
--   Let $\tau(10)$ be the kissing number in dimension $10$: the largest size of a finite set of unit vectors in $\mathbb{R}^{10}$ with pairwise inner products at most $\tfrac12$. Then
--   $$
--   \tau(10) \;\ge\; 500.
--   $$
--
--   An explicit configuration: take the $2\cdot10$ vectors $\pm 2e_i$ together with, for each of 30 four-element subsets $S$ of $\{1,\dots,10\}$ chosen so that any two of them share at most two points, the $16$ vectors that are $\pm1$ on $S$ and $0$ elsewhere; all have squared norm $4$ and pairwise inner products at most $2$, so after rescaling by $\tfrac12$ they are $2\cdot10+16\cdot 30=500$ unit vectors with pairwise inner products at most $\tfrac12$. (This is Construction A applied to a binary constant-weight code of length $10$, distance $4$, size $30$.) The exact value of $\tau(10)$ is not known.
--
--   **Formalization Note** The kissing number is the platform's `KissingNumber.kissingNumber 10 : ℕ∞`, the supremum, over all `KissingConfig 10` (a `Finset` of vectors of `EuclideanSpace ℝ (Fin 10)` of norm exactly $1$ with pairwise real inner product at most $1/2$ between distinct members), of the cardinality. The statement is `(500 : ℕ∞) ≤ kissingNumber 10`; no upper bound is asserted.
--
--   **Why this is a variation.** Variation on the open mission 'The Kissing Number Problem' (parent theorems KissingNumber.kissing_number_three, _four, _five, _eight, _twentyfour). It is the lower half of the determination of tau(10), stated with the parent's own KissingNumber definitions, a partial result with an explicit finite configuration of 500 points; improving it or matching an upper bound is exactly the open problem in this dimension.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999: Construction A and the non-lattice packing P10b in dimension 10, kissing number 500 (Chapter 5 and the table of kissing numbers in Chapter 1; section and table numbers cited from memory). Truth check: the author built the 500 vectors described above from 30 four-element subsets of a 10-point set pairwise meeting in at most two points (found by computer search) and verified by computer that they are 500 distinct vectors of squared norm 4 with all pairwise inner products at most 2. Larger kissing configurations in dimension 10 may be known; only the lower bound 500 is asserted. Origin: the open mission 'The Kissing Number Problem'.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations

open KissingNumber

/-- Lower bound for the kissing number in dimension 10: `500 ≤ τ(10)`, by an explicit configuration. -/
theorem kissing_number_ten_lower : (500 : ℕ∞) ≤ kissingNumber 10 := by
  sorry

end LefebvreVariations
