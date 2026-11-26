-- Prove2me | Theorems.Thm_LefebvreVariations_kissing_number_seven_lower
-- name    : LefebvreVariations.kissing_number_seven_lower
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:20:21.648073+00:00
-- url     : https://prove2.me/theorems/e00381a9-e7ce-4327-a3b2-b61db7481808
-- title:
--   Lefebvre's variations, No. 38 — on a theme by Conway and Sloane: the kissing number in dimension 7 is at least 126
-- statement:
--   Let $\tau(7)$ be the kissing number in dimension $7$: the largest number of non-overlapping unit balls in $\mathbb{R}^{7}$ that can touch a common unit ball, equivalently the largest size of a finite set of unit vectors in $\mathbb{R}^{7}$ with pairwise inner products at most $\tfrac12$. Then
--   $$
--   \tau(7) \;\ge\; 126.
--   $$
--
--   The bound is attained by the $126$ minimal vectors of the root lattice $E_7$ (its roots), rescaled to unit length: they are unit vectors whose pairwise inner products are $\le \tfrac12$. The exact value of $\tau(7)$ is not known; the best known upper bound is $134$ (semidefinite programming bounds of Mittelmann and Vallentin), so this is the lower half of an open determination.
--
--   **Formalization Note** The kissing number is the platform's `KissingNumber.kissingNumber 7 : ℕ∞`, the supremum, over all `KissingConfig 7` (a `Finset` of vectors of `EuclideanSpace ℝ (Fin 7)` of norm exactly $1$ with pairwise real inner product at most $1/2$ between distinct members), of the cardinality. The statement is `(126 : ℕ∞) ≤ kissingNumber 7`: there is such a configuration with at least $126$ points. No upper bound is asserted.
--
--   **Why this is a variation.** This varies the kissing number problem in dimension 7, which asks for $\tau(7)$, an open exact value. It is the lower half of the parent: $126\le\tau(7)$, realised by an explicit configuration, namely the roots of $E_7$. Any proof of the exact value needs this bound on one side, so a matching upper bound would settle the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999: the lattice E7 and its minimal vectors (Chapter 4), and the table of kissing numbers in Chapter 1 giving the lower bound 126 in dimension 7 (cited from memory: table and section numbers not re-checked). The exact value of the kissing number in dimension 7 is open; the statement here is the lower bound given by the roots of E7. The upper bound quoted in the text (134) is from memory (semidefinite-programming bounds of Bachoc-Vallentin / Mittelmann-Vallentin) and is not part of the formal statement. Origin of this statement: it is the lower half of the determination of KissingNumber.kissingNumber 7, the open-ended mission 'The Kissing Number Problem' (parent theorems KissingNumber.kissing_number_three, _four, _five, _eight, _twentyfour); the statement is not claimed from a source beyond the explicit configuration.

import Definitions.Def_KissingNumber

set_option autoImplicit false

namespace LefebvreVariations

open KissingNumber

/-- Lower half of the value of the kissing number in dimension 7: `126 ≤ τ(7)`, by an explicit configuration. -/
theorem kissing_number_seven_lower : (126 : ℕ∞) ≤ kissingNumber 7 := by
  sorry

end LefebvreVariations
