-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_Weighted_finite_dual_domination
-- name    : OAI.ProjectionMoments.Weighted.finite_dual_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:18:59.606922+00:00
-- url     : https://prove2.me/theorems/55020d08-8508-44d0-ab66-d0bd0b6821aa
-- title:
--   Finite linear-programming duality for weighted covers
-- statement:
--   For weights $b_i\ge1$ indexed by a set $\iota$ and $K\ge0$, the budget set is $\mathcal B(b,K)=\{a\in\mathbb R^\iota:a_i\ge0,\ \sum_{i\in s}a_ib_i\le K\text{ for every finite }s\}$, with the product topology. Assume that only finitely many $i$ satisfy $b_i\le R$, for each $R$, and let $K>0$. Let $J$ be finite, let $v_j\in[0,1]^\iota$ and $y_j\in\mathbb R$ for $j\in J$. Suppose every $c\in\mathbb R_{\ge0}^J$ with $\sum_jc_jv_{j,i}\le b_i$ for all $i$ satisfies $\sum_jc_jy_j\le K$. Then there is $a\in\mathcal B(b,K)$ with
--   $$
--   y_j\le\sum_ia_i\,v_{j,i}\qquad\text{for all }j\in J .
--   $$
--
--   This is the covering form of linear programming duality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/WeightedCover.lean#L174-L260

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover

open OAI OAI.ProjectionMoments OAI.ProjectionMoments.Weighted
open scoped Topology BigOperators Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
variable {ι : Type*}

theorem OAI.ProjectionMoments.Weighted.finite_dual_domination {J : Type*} [Fintype J] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K) (v : J → ι → ℝ) (hv : ∀ j i, v j i ∈ Icc (0:ℝ) 1)
    (y : J → ℝ)
    (hdual : ∀ c : J → ℝ, (∀ j, 0 ≤ c j) →
      (∀ i, ∑ j, c j*v j i ≤ b i) → ∑ j, c j*y j ≤ K) :
    ∃ a ∈ budget b K, ∀ j, y j ≤ ∑' i, a i*v j i := by sorry
