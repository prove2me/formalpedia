-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_six_lower
-- name    : LefebvreVariations.kissing_number_six_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:19:36.259128+00:00
-- url     : https://prove2.me/theorems/fb0c2bdb-9360-5ff8-8e37-1dd0a1c1feea
-- title:
--   Lefebvre's variations, No. 37 — on a theme by Conway and Sloane: the kissing number in dimension 6 is at least 72
-- statement:
--   Let $\tau(6)$ be the kissing number in dimension $6$: the largest number of non-overlapping unit balls in $\mathbb{R}^{6}$ that can touch a common unit ball, equivalently the largest size of a finite set of unit vectors in $\mathbb{R}^{6}$ with pairwise inner products at most $\tfrac12$. Then
--   $$
--   \tau(6) \;\ge\; 72.
--   $$
--
--   The bound is attained by the $72$ minimal vectors of the root lattice $E_6$ (its roots), rescaled to unit length: they are unit vectors whose pairwise inner products are $\le \tfrac12$. The exact value of $\tau(6)$ is not known; the best known upper bound is $77$ (semidefinite programming bounds of Mittelmann and Vallentin), so this is the lower half of an open determination.
--
--   **Formalization Note** The kissing number is the platform's `KissingNumber.kissingNumber 6 : ℕ∞`, the supremum, over all `KissingConfig 6` (a `Finset` of vectors of `EuclideanSpace ℝ (Fin 6)` of norm exactly $1$ with pairwise real inner product at most $1/2$ between distinct members), of the cardinality. The statement is `(72 : ℕ∞) ≤ kissingNumber 6`: there is such a configuration with at least $72$ points. No upper bound is asserted.
--
--   **Why this is a variation.** This varies the kissing number problem in dimension 6, which asks for $\tau(6)$, an open exact value. It is the lower half of the parent: $72\le\tau(6)$, realised by an explicit configuration, namely the roots of $E_6$. Any proof of the exact value needs this bound on one side, so a matching upper bound would settle the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999: the lattice E6 and its minimal vectors (Chapter 4), and the table of kissing numbers in Chapter 1 giving the lower bound 72 in dimension 6 (cited from memory: table and section numbers not re-checked). The exact value of the kissing number in dimension 6 is open; the statement here is the lower bound given by the roots of E6. The upper bound quoted in the text (77) is from memory (semidefinite-programming bounds of Bachoc-Vallentin / Mittelmann-Vallentin) and is not part of the formal statement. Origin of this statement: it is the lower half of the determination of KissingNumber.kissingNumber 6, the open-ended mission 'The Kissing Number Problem' (parent theorems KissingNumber.kissing_number_three, _four, _five, _eight, _twentyfour); the statement is not claimed from a source beyond the explicit configuration.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations

open KissingNumber

/-- Lower half of the value of the kissing number in dimension 6: `72 ≤ τ(6)`, by an explicit configuration. -/
theorem kissing_number_six_lower : (72 : ℕ∞) ≤ kissingNumber 6 := by
  sorry

end LefebvreVariations
