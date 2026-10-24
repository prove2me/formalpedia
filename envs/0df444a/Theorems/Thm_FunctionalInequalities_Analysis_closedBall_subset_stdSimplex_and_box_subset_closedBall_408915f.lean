-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_closedBall_subset_stdSimplex_and_box_subset_closedBall_408915f
-- name    : FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:33.973368+00:00
-- url     : https://prove2.me/theorems/0beb910c-3087-4fd3-8d2f-8132f5f9fda2
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
--   The declaration is `closedBall_subset_stdSimplex_and_box_subset_closedBall`. The dimension restriction is strictly $0<n$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean#L346-L501 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Normalization`, declaration `FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Mathlib

noncomputable section
open Set Matrix
section LT11D3SimplexBall
open Set Metric
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall_408915f {n : ℕ} (hn : 0 < n) :
    closedBall ((1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ))
        (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) ⊆
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} ∧
    {y : EuclideanSpace ℝ (Fin n) | (∀ i, |y i| ≤ 1) ∧ |1 - ∑ i, y i| ≤ 1} ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) := by sorry
