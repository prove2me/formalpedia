-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_Weighted_measure_domination
-- name    : OAI.ProjectionMoments.Weighted.measure_domination
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:20:32.276679+00:00
-- url     : https://prove2.me/theorems/68d34648-0cc7-4e73-82c5-5aefd8f1b53d
-- title:
--   Dual criterion for domination by weighted sums of probability measures
-- statement:
--   Let $\mu$ be a finite measure and $(P_i)_{i\in\iota}$ a countable family of probability measures on a measurable space. Let $b_i\ge1$ be such that only finitely many $i$ satisfy $b_i\le R$, for each $R$, and let $K>0$. Assume every bounded measurable $h\ge0$ with $\int h\,dP_i\le b_i$ for all $i$ satisfies $\int h\,d\mu\le K$. Then there are $a_i\ge0$ with $\sum_ia_ib_i$ summable,
--   $$
--   \sum_ia_ib_i\le K\qquad\text{and}\qquad\mu\le\sum_ia_iP_i .
--   $$
--
--   The dual test condition thus produces an explicit dominating combination of the $P_i$ with controlled cost.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/WeightedCover.lean#L304-L360

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
variable {Ω ι : Type*} [MeasurableSpace Ω]

theorem OAI.ProjectionMoments.Weighted.measure_domination [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : ι → Measure Ω) [∀ i, IsProbabilityMeasure (P i)] {b : ι → ℝ}
    (hb : ∀ i, 1 ≤ b i) (hproper : ∀ R : ℝ, {i | b i ≤ R}.Finite)
    {K : ℝ} (hK : 0 < K)
    (hdual : ∀ h : Ω → ℝ≥0∞, Measurable h →
      (∃ H : ℝ≥0, ∀ x, h x ≤ H) →
      (∀ i, ∫⁻ x, h x ∂P i ≤ ENNReal.ofReal (b i)) →
      ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal K) :
    ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ Summable (fun i => a i*b i) ∧ (∑' i, a i*b i) ≤ K ∧
      μ ≤ Measure.sum (fun i => ENNReal.ofReal (a i) • P i) := by sorry
