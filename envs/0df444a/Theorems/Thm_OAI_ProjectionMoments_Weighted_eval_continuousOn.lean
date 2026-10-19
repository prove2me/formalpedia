-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_Weighted_eval_continuousOn
-- name    : OAI.ProjectionMoments.Weighted.eval_continuousOn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:17:23.648895+00:00
-- url     : https://prove2.me/theorems/9e1768a2-842d-4dda-a8cb-0227e5d5de8d
-- title:
--   Continuity of weighted evaluations on the budget set
-- statement:
--   For weights $b_i\ge1$ indexed by a set $\iota$ and $K\ge0$, the budget set is $\mathcal B(b,K)=\{a\in\mathbb R^\iota:a_i\ge0,\ \sum_{i\in s}a_ib_i\le K\text{ for every finite }s\}$, with the product topology. Assume that for each $R$ only finitely many $i$ satisfy $b_i\le R$. Then for every $v\in[0,1]^\iota$ the evaluation
--   $$
--   a\longmapsto\sum_{i}a_i\,v_i
--   $$
--   is continuous on $\mathcal B(b,K)$.
--
--   Continuity holds even though the sum has infinitely many terms, because the budget forces uniformly small tails.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/WeightedCover.lean#L104-L130

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

theorem OAI.ProjectionMoments.Weighted.eval_continuousOn {b : ι → ℝ} (hb : ∀ i, 1 ≤ b i)
    (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite) {K : ℝ} (hK : 0 ≤ K)
    {v : ι → ℝ} (hv : ∀ i, v i ∈ Icc (0:ℝ) 1) :
    ContinuousOn (fun a : ι → ℝ => ∑' i, a i*v i) (budget b K) := by sorry
