-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_abs_simplexCoord_le_one_of_max_408915f
-- name    : FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:14.119387+00:00
-- url     : https://prove2.me/theorems/dfaee466-db18-41cc-a581-25c7a2df1e0b
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
--   The declaration `abs_simplexCoord_le_one_of_max` is a reusable box bound for coordinates relative to a maximal-volume nondegenerate simplex. No convexity of $K$ is assumed explicitly.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L172-L296 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Mathlib

noncomputable section
open Set Matrix
section LT11D2MaxSimplexBox
open Set Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max_408915f {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)} (hv : ∀ i, v i ∈ K)
    (hdet : (simplexEdgeMatrix v).det ≠ 0)
    (hmax : ∀ w : Fin (n + 1) → EuclideanSpace ℝ (Fin n), (∀ i, w i ∈ K) →
      |(simplexEdgeMatrix w).det| ≤ |(simplexEdgeMatrix v).det|)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ K) :
    (∀ j, |((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1) ∧
      |1 - ∑ j, ((simplexEdgeMatrix v)⁻¹ *ᵥ (y - v 0 : EuclideanSpace ℝ (Fin n)).ofLp) j| ≤ 1 := by sorry
