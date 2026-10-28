-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_abs_simplexCoord_le_one_of_max_readable
-- name    : FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:31.354548+00:00
-- url     : https://prove2.me/theorems/8c17d6d3-6bb3-4149-817e-62c066eb1e35
-- title:
--   Simplex Coordinates Bounded by Maximality
-- statement:
--   This is an auxiliary geometric statement for affine normalization of a convex body.
--
--   Let $n\in\mathbb N$, let $K\subseteq \operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$, and let $v_0,\ldots,v_n\in K$. Write $M=\operatorname{simplexEdgeMatrix}(v)$ and assume:
--
--   1. $\det M\ne 0$.
--   2. For every $w_0,\ldots,w_n\in K$, $|\det(\operatorname{simplexEdgeMatrix}(w))|\le |\det M|$.
--
--   Then every $y\in K$ has simplex coordinates $c=M^{-1}(y-v_0)$ satisfying
--
--   $$|c_j|\le 1\quad\text{for every }j<n,
--   \qquad \left|1-\sum_{j<n}c_j\right|\le 1.$$
--
--   The declaration `abs_simplexCoord_le_one_of_max_readable` is a reusable box bound for coordinates relative to a maximal-volume nondegenerate simplex. No convexity of $K$ is assumed explicitly.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem abs_simplexCoord_le_one_of_max {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
--       {v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, v i ∈ K)
--       (hdet : (simplexEdgeMatrix v).det ≠ 0)
--       (hmax : ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
--         |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det|)
--       {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ K) :
--       (∀ j, |((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1) ∧
--         |1 - ∑ j, ((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Normalization`](https://prove2.me/theorems/c20810ec-8464-4452-b023-bf292cc5b276).
--
--   Previous: [`exists_max_simplexEdgeMatrix_det`](https://prove2.me/theorems/20479a29-7d2f-4cb5-8d1b-e0dbc2e4e013) · Next: [`closedBall_subset_stdSimplex_and_box_subset_closedBall`](https://prove2.me/theorems/13e62e66-a24e-43f3-9ca6-0687c2a3f734).
--
--   [Source excerpt, lines 176–183](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L176-L183) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L172-L296 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization

open Set Matrix

theorem FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max_readable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, v i ∈ K)
    (hdet : (simplexEdgeMatrix v).det ≠ 0)
    (hmax : ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
      |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det|)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ K) :
    (∀ j, |((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1) ∧
      |1 - ∑ j, ((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1 := by sorry
