-- Prove2me | Theorems.Thm_LefebvreVariations_kneser_poulsen_line
-- name    : LefebvreVariations.kneser_poulsen_line
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:49:55.412449+00:00
-- url     : https://prove2.me/theorems/3cd0bf0f-1bf2-51db-a3f0-2738d953462a
-- title:
--   Lefebvre's variations, No. 92 — on a theme by Kneser and Poulsen: the Kneser–Poulsen conjecture on the line
-- statement:
--   For all $n$, centres $p_1,\dots,p_n$ and $q_1,\dots,q_n$ in $\mathbb{R}$ and radii $\rho_1,\dots,\rho_n>0$ with $|q_i-q_j|\le|p_i-p_j|$ for all $i,j$,
--   $$
--   \Big|\bigcup_{i=1}^n (q_i-\rho_i,\,q_i+\rho_i)\Big|\;\le\;\Big|\bigcup_{i=1}^n (p_i-\rho_i,\,p_i+\rho_i)\Big|,
--   $$
--   where $|\cdot|$ is Lebesgue measure.
--
--   This is the one-dimensional case of the Kneser–Poulsen conjecture: contracting the centres of finitely many balls does not increase the volume of their union. In dimension one it is an elementary fact; the conjecture is a theorem in the plane (Bezdek and Connelly) and open in dimension $d\ge 3$.
--
--   **Formalization Note** The statement is the platform's `kneser_poulsen_conjecture` with `d = 1` fixed (`EuclideanSpace ℝ (Fin 1)`), the redundant hypothesis `1 ≤ d` dropped. Radii may differ, `n = 0` is allowed (both sides `0`), and the balls are open. The volume is Lebesgue measure valued in `ℝ≥0∞`.
--
--   **Why this is a variation.** Special case of the open platform problem kneser_poulsen_conjecture (the formal statement for all dimensions d >= 1 is marked Open there). It fixes d = 1, the smallest dimension the parent allows, where the statement is elementary; the conjecture remains open mathematically for every d >= 3.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: kneser_poulsen_conjecture (status Open on the platform for the formal statement with all d >= 1); this is the case d = 1, which is classical and elementary (no source needed; checked numerically on 50000 random contractions of the line, no violation).
--   Context: the planar case is Bezdek and Connelly, J. reine angew. Math. 553 (2002), 221-236 (verified); the conjecture is attributed to Kneser (1955) and Poulsen (1954).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The Kneser–Poulsen conjecture on the line: contracting the centres of finitely many intervals
of arbitrary radii does not increase the length of the union. -/
theorem kneser_poulsen_line (n : ℕ)
    (centers : Fin n → EuclideanSpace ℝ (Fin 1))
    (centers' : Fin n → EuclideanSpace ℝ (Fin 1))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hcontract : ∀ i j : Fin n, dist (centers' i) (centers' j) ≤ dist (centers i) (centers j)) :
    MeasureTheory.volume (⋃ i, Metric.ball (centers' i) (r i)) ≤
    MeasureTheory.volume (⋃ i, Metric.ball (centers i) (r i)) := by
  sorry

end LefebvreVariations
