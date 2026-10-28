-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_max_simplexEdgeMatrix_det_readable
-- name    : FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:39.583228+00:00
-- url     : https://prove2.me/theorems/20479a29-7d2f-4cb5-8d1b-e0dbc2e4e013
-- title:
--   Maximal Positive-Volume Simplex in a Compact Set
-- statement:
--   This establishes existence of a maximal-volume simplex in a compact set with nonempty interior.
--
--   Let $K\subseteq\mathbb R^n$ be compact and assume $\operatorname{int}(K)\ne\varnothing$. Then there exists a map $v:\operatorname{Fin}(n+1)\to\mathbb R^n$ such that:
--
--   1. Every vertex $v_i$ belongs to $K$.
--   2. The simplex edge matrix has positive determinant magnitude:
--      $$|\det(\operatorname{simplexEdgeMatrix}(v))|>0.$$
--   3. Every other $(n+1)$-tuple $w$ of points in $K$ has no larger determinant magnitude:
--      $$|\det(\operatorname{simplexEdgeMatrix}(w))|\le|\det(\operatorname{simplexEdgeMatrix}(v))|.$$
--
--   The declaration is `exists_max_simplexEdgeMatrix_det_readable`. It is the compactness and normalization step for selecting a nondegenerate maximal simplex.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_max_simplexEdgeMatrix_det {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
--       (hK : IsCompact K) (hint : (interior K).Nonempty) :
--       ∃ v : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, v i ∈ K) ∧
--         0 < |(simplexEdgeMatrix v).det| ∧
--         ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
--           |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det|
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Normalization`](https://prove2.me/theorems/c20810ec-8464-4452-b023-bf292cc5b276).
--
--   Next: [`abs_simplexCoord_le_one_of_max`](https://prove2.me/theorems/8c17d6d3-6bb3-4149-817e-62c066eb1e35).
--
--   [Source excerpt, lines 31–36](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L31-L36) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L29-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization

theorem FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det_readable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hint : (interior K).Nonempty) :
    ∃ v : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, v i ∈ K) ∧
      0 < |(simplexEdgeMatrix v).det| ∧
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
        |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det| := by sorry
