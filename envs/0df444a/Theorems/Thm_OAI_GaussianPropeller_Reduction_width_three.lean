-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_width_three
-- name    : OAI.GaussianPropeller.Reduction.width_three
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:27:06.39122+00:00
-- url     : https://prove2.me/theorems/87d02985-7d3c-4ebb-8280-974aa1ab6378
-- title:
--   The Gaussian width of three score vectors
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$ and $v_0,v_1,v_2\in\mathbb R^d$. Then
--   $$
--   \int\max_i\langle v_i,x\rangle\,d\gamma_d(x)=\frac{|v_0-v_1|+|v_0-v_2|+|v_1-v_2|}{2\sqrt{2\pi}} .
--   $$
--
--   For three cells the width depends only on the side lengths of the triangle of score vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Attainment.lean#L91-L116

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
universe uE
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem OAI.GaussianPropeller.Reduction.width_three {d : ℕ} (v : Tuple d 3) :
    width v = (‖v.ofLp 0 - v.ofLp 1‖ + ‖v.ofLp 0 - v.ofLp 2‖ +
      ‖v.ofLp 1 - v.ofLp 2‖) / (2 * Real.sqrt (2 * Real.pi)) := by sorry
