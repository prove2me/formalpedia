-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_HeatMaximum_min_gradient_left
-- name    : OAI.GaussianPropeller.HeatMaximum.min_gradient_left
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:09:59.419443+00:00
-- url     : https://prove2.me/theorems/20506603-f5aa-4301-b0c5-21590e30a1a0
-- title:
--   First-order condition at a minimum of the concavity deficit
-- statement:
--   Let $v$ be differentiable with gradient $p$ on a real inner product space. For weights $a,b$ and slack $\sigma$, let $\delta(x,y)=v(ax+by)-a\,v(x)-b\,v(y)+\sigma\bigl(1+a|x|^2+b|y|^2\bigr)$. If $a>0$ and $(x,y)$ minimizes $\delta$ globally, then
--   $$
--   p(ax+by)-p(x)=-2\sigma\,x .
--   $$
--
--   The analogous identity holds in the second variable, which pins down the gradients at a minimum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/HeatMaximum.lean#L130-L160

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatMaximum
universe uE uι
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
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.GaussianPropeller.HeatMaximum.min_gradient_left {v : E → ℝ} {p : E → E} {a b σ : ℝ} {x y : E}
    (hp : ∀ x, HasFDerivAt v (innerSL ℝ (p x)) x) (ha : 0 < a)
    (hm : ∀ x' y', deficit v a b σ x y ≤ deficit v a b σ x' y') :
    p (a • x+b • y)-p x = -(2*σ) • x := by sorry
