-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_max_simplexEdgeMatrix_det_408915f
-- name    : FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:41.822594+00:00
-- url     : https://prove2.me/theorems/72638a82-6db4-4681-aa35-2d75bf0cae27
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
--   The declaration is `exists_max_simplexEdgeMatrix_det`. It is the compactness and normalization step for selecting a nondegenerate maximal simplex.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L29-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Mathlib

noncomputable section
open Set Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det_408915f {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hint : (interior K).Nonempty) :
    ∃ v : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, v i ∈ K) ∧
      0 < |(simplexEdgeMatrix v).det| ∧
      ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
        |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det| := by sorry
