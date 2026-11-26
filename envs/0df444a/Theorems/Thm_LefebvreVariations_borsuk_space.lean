-- Prove2me | Theorems.Thm_LefebvreVariations_borsuk_space
-- name    : LefebvreVariations.borsuk_space
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:52:32.81532+00:00
-- url     : https://prove2.me/theorems/cce0f654-327e-5228-965e-8971b4884ad3
-- title:
--   Lefebvre's variations, No. 100 — on a theme by Borsuk: Borsuk's conjecture in dimension three
-- statement:
--   Let $S\subset\mathbb{R}^3$ be a bounded set with $\operatorname{diam}S>0$. Then $S=A\cup B\cup C\cup D$ for four sets each of diameter strictly smaller than $\operatorname{diam}S$.
--
--   This is the three-dimensional case of Borsuk's conjecture: every bounded subset of $\mathbb{R}^d$ of positive diameter is a union of $d+1$ sets of smaller diameter. The conjecture holds for $d\le 3$, fails for $d\ge 64$ (Kahn–Kalai and successors), and is open for $4\le d\le 63$.
--
--   **Formalization Note** `S : Set (EuclideanSpace ℝ (Fin 3))` with `Bornology.IsBounded S` and `0 < Metric.diam S`; the diameters are the real `Metric.diam`. The conclusion is an equality of sets `S = A ∪ B ∪ C ∪ D` with all four diameters `< Metric.diam S`. The hypothesis of positive diameter rules out the one-point set and the empty set.
--
--   **Why this is a variation.** Special case d = 3 of Borsuk's conjecture (every bounded subset of R^d of positive diameter is a union of d+1 sets of smaller diameter). It is a theorem, the last dimension where the conjecture is known; it is open for 4 <= d <= 63. No open parent entry was found on the platform by keyword search.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): Borsuk's conjecture in R^d (open for 4 <= d <= 63); no matching open platform entry. This is the case d = 3.
--   Verified by search (historical account): J. Perkal announced the case d = 3 in 1947 without proof; H. G. Eggleston gave the first detailed proof in 1955; B. Grunbaum and A. Heppes gave simple proofs in 1957. Exact titles, journals and pages are cited from memory and not verified (Eggleston, J. London Math. Soc. 30 (1955); Perkal, Colloq. Math. 2 (1947)).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Borsuk's conjecture in dimension three: every bounded set of positive diameter in ℝ³ is a
union of four sets of strictly smaller diameter. -/
theorem borsuk_space (S : Set (EuclideanSpace ℝ (Fin 3)))
    (hb : Bornology.IsBounded S) (hd : 0 < Metric.diam S) :
    ∃ A B C D : Set (EuclideanSpace ℝ (Fin 3)), S = A ∪ B ∪ C ∪ D ∧
      Metric.diam A < Metric.diam S ∧ Metric.diam B < Metric.diam S ∧
      Metric.diam C < Metric.diam S ∧ Metric.diam D < Metric.diam S := by
  sorry

end LefebvreVariations
