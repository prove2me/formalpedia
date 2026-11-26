-- Prove2me | Theorems.Thm_LefebvreVariations_kneser_poulsen_plane
-- name    : LefebvreVariations.kneser_poulsen_plane
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:49:42.021575+00:00
-- url     : https://prove2.me/theorems/b54917e8-ef10-4ebf-b162-70f0d5c32674
-- title:
--   Lefebvre's variations, No. 66 — on a theme by Kneser and Poulsen: the Kneser–Poulsen conjecture in the plane
-- statement:
--   Let $D(c,\rho)$ denote the open disc of centre $c$ and radius $\rho$ in $\mathbb{R}^2$. For all $n$, centres $p_1,\dots,p_n$ and $q_1,\dots,q_n$ in $\mathbb{R}^2$ and radii $\rho_1,\dots,\rho_n>0$ with $|q_i-q_j|\le|p_i-p_j|$ for all $i,j$,
--   $$
--   \operatorname{area}\Big(\bigcup_{i=1}^n D(q_i,\rho_i)\Big)\;\le\;\operatorname{area}\Big(\bigcup_{i=1}^n D(p_i,\rho_i)\Big).
--   $$
--
--   This is the planar case of the Kneser–Poulsen conjecture: if the centres of finitely many balls are moved so that no pairwise distance increases, the volume of their union does not increase. In the plane it was proved by Bezdek and Connelly; it remains open in dimension $d\ge 3$.
--
--   **Formalization Note** The statement is the platform's `kneser_poulsen_conjecture` with `d = 2` fixed (`EuclideanSpace ℝ (Fin 2)`) and the redundant hypothesis `1 ≤ d` dropped. Radii may differ from disc to disc, `n = 0` is allowed (both sides are `0`), `MeasureTheory.volume` is the Lebesgue measure of the plane valued in `ℝ≥0∞`, and the balls are open (`Metric.ball`).
--
--   **Why this is a variation.** Special case of the open platform problem kneser_poulsen_conjecture (the formal statement for all dimensions d >= 1 is marked Open there). It fixes d = 2, where the statement is a theorem of Bezdek and Connelly (2002); the conjecture remains open mathematically for every d >= 3.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: kneser_poulsen_conjecture (Kneser-Poulsen conjecture in R^d, status Open on the platform for the formal statement with all d >= 1); this is the case d = 2, which is a theorem of Bezdek and Connelly.
--   Bezdek and Connelly, 'Pushing disks apart - the Kneser-Poulsen conjecture in the plane', J. reine angew. Math. 553 (2002), 221-236 (journal reference and authorship verified on the authors' page and arXiv math/0108098; the statement covers finite unions of discs with arbitrary radii). The conjecture itself is attributed to Kneser (1955) and Poulsen (1954), as stated in the abstract of that paper.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The Kneser–Poulsen conjecture in the plane (Bezdek–Connelly): moving the centres of finitely
many discs of arbitrary radii so that no pairwise distance increases does not increase the area of
the union. -/
theorem kneser_poulsen_plane (n : ℕ)
    (centers : Fin n → EuclideanSpace ℝ (Fin 2))
    (centers' : Fin n → EuclideanSpace ℝ (Fin 2))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hcontract : ∀ i j : Fin n, dist (centers' i) (centers' j) ≤ dist (centers i) (centers j)) :
    MeasureTheory.volume (⋃ i, Metric.ball (centers' i) (r i)) ≤
    MeasureTheory.volume (⋃ i, Metric.ball (centers i) (r i)) := by
  sorry

end LefebvreVariations
