-- Prove2me | Theorems.Thm_LefebvreVariations_borsuk_plane
-- name    : LefebvreVariations.borsuk_plane
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:52:16.564079+00:00
-- url     : https://prove2.me/theorems/c5a954bf-ef8c-551a-bd33-47892a1558c7
-- title:
--   Lefebvre's variations, No. 71 — on a theme by Borsuk: Borsuk's conjecture in the plane
-- statement:
--   Let $S\subset\mathbb{R}^2$ be a bounded set with $\operatorname{diam}S>0$. Then $S=A\cup B\cup C$ for three sets $A,B,C$ each of diameter strictly smaller than $\operatorname{diam}S$.
--
--   This is the planar case of Borsuk's conjecture: every bounded subset of $\mathbb{R}^d$ of positive diameter is a union of $d+1$ sets of smaller diameter. The conjecture is known for $d\le 3$, false for $d\ge 64$ (Kahn–Kalai, with later improvements), and open for $4\le d\le 63$.
--
--   **Formalization Note** `S : Set (EuclideanSpace ℝ (Fin 2))` with `Bornology.IsBounded S` and `0 < Metric.diam S`; the diameters are the real `Metric.diam`. The conclusion is an equality of sets `S = A ∪ B ∪ C` (not only an inclusion) with `Metric.diam A`, `Metric.diam B`, `Metric.diam C` all `< Metric.diam S`. The hypothesis of positive diameter rules out the one-point set and the empty set.
--
--   **Why this is a variation.** Special case d = 2 of Borsuk's conjecture (every bounded subset of R^d of positive diameter is a union of d+1 sets of smaller diameter). It is a classical theorem of Borsuk; the conjecture is false for large d and open for 4 <= d <= 63. No open parent entry was found on the platform by keyword search.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): Borsuk's conjecture in R^d (open for 4 <= d <= 63); no matching open platform entry (the platform has the failure in dimension 1325, ProofsInTheBook.Chapter16.not_borsukConjecture_1325). This is the case d = 2.
--   Source: K. Borsuk, 'Drei Saetze ueber die n-dimensionale euklidische Sphaere', Fund. Math. 20 (1933), 177-190 (volume and year confirmed by search; that the plane case is in this paper is cited from memory). Counterexamples in high dimension: Kahn and Kalai, Bull. Amer. Math. Soc. 29 (1993) (cited from memory).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Borsuk's conjecture in the plane: every bounded planar set of positive diameter is a union of
three sets of strictly smaller diameter. -/
theorem borsuk_plane (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hb : Bornology.IsBounded S) (hd : 0 < Metric.diam S) :
    ∃ A B C : Set (EuclideanSpace ℝ (Fin 2)), S = A ∪ B ∪ C ∧
      Metric.diam A < Metric.diam S ∧ Metric.diam B < Metric.diam S ∧
      Metric.diam C < Metric.diam S := by
  sorry

end LefebvreVariations
