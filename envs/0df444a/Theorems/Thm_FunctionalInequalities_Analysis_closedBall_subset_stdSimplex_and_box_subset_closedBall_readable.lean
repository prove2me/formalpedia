-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_closedBall_subset_stdSimplex_and_box_subset_closedBall_readable
-- name    : FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:44.712786+00:00
-- url     : https://prove2.me/theorems/13e62e66-a24e-43f3-9ca6-0687c2a3f734
-- title:
--   Simplex Ball Inclusion and Box Ball Inclusion
-- statement:
--   This establishes two elementary geometric inclusions for the standard simplex and a coordinate box.
--
--   Let $n\ge1$ and work in $\mathbb R^n=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$. Let
--
--   $$
--   c=\frac1{n+1}\sum_i e_i,
--   \qquad
--   \rho=\frac1{2(n+1)\sqrt n}.
--   $$
--
--   Then
--
--   $$
--   \overline B(c,\rho)\subseteq\left\{y: y_i\ge0\ \forall i,\ \sum_i y_i\le1\right\},
--   $$
--
--   and
--
--   $$
--   \left\{y: |y_i|\le1\ \forall i,\ \left|1-\sum_i y_i\right|\le1\right\}
--   \subseteq\overline B(0,\sqrt n).
--   $$
--
--   The declaration is `closedBall_subset_stdSimplex_and_box_subset_closedBall_readable`. The dimension restriction is strictly $0<n$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem closedBall_subset_stdSimplex_and_box_subset_closedBall {n : ℕ} (hn : 0 < n) :
--       closedBall ((1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ))
--           (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) ⊆
--         {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} ∧
--       {y : EuclideanSpace ℝ (Fin n) | (∀ i, |y i| ≤ 1) ∧ |1 - ∑ i, y i| ≤ 1} ⊆
--         closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Normalization`](https://prove2.me/theorems/c20810ec-8464-4452-b023-bf292cc5b276).
--
--   Previous: [`abs_simplexCoord_le_one_of_max`](https://prove2.me/theorems/8c17d6d3-6bb3-4149-817e-62c066eb1e35) · Next: [`exists_affine_normalization`](https://prove2.me/theorems/eaae9cde-a1a3-4aa1-8fc7-b6ed5d522bb4).
--
--   [Source excerpt, lines 348–353](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L348-L353) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L346-L501 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization

open Set Metric

theorem FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall_readable {n : ℕ} (hn : 0 < n) :
    closedBall ((1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ))
        (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) ⊆
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} ∧
    {y : EuclideanSpace ℝ (Fin n) | (∀ i, |y i| ≤ 1) ∧ |1 - ∑ i, y i| ≤ 1} ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) := by sorry
