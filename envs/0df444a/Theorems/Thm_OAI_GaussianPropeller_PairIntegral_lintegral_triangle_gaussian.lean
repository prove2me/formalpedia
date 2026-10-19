-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_PairIntegral_lintegral_triangle_gaussian
-- name    : OAI.GaussianPropeller.PairIntegral.lintegral_triangle_gaussian
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:33:21.784681+00:00
-- url     : https://prove2.me/theorems/cb69f580-3e62-4bcf-9d60-761ff58d1c04
-- title:
--   A Gaussian integral of the triangle function
-- statement:
--   Let $\Delta(s,u,v)=\max(s+u+v,0)$ when $u\le s$ and $v\le s$, and $\Delta=0$ otherwise. Let $N_1,N_2,N_3$ be independent standard normal variables, $a,c>0$ and $b\in\mathbb R$. Then
--   $$
--   \mathbb E\,\Delta\bigl(N_1,\ aN_2,\ bN_2+cN_3\bigr)\le\frac{9}{2\pi\sqrt{2\pi}\,a\,c}.
--   $$
--
--   This controls how a cell's centroid interacts with two orthogonal residual directions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/PairIntegral.lean#L248-L274

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
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.PairIntegral
universe uX
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal

theorem OAI.GaussianPropeller.PairIntegral.lintegral_triangle_gaussian {a c : ℝ} (b : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ s : ℝ, (∫⁻ x : ℝ, (∫⁻ y : ℝ, triangle s (a*x) (b*x+c*y)
      ∂gaussianReal 0 1) ∂gaussianReal 0 1) ∂gaussianReal 0 1 ≤
      ENNReal.ofReal (9/(2*Real.pi*Real.sqrt (2*Real.pi)*a*c)) := by sorry
