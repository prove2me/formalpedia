-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_SoftMin_Z_fderiv
-- name    : OAI.GaussianPropeller.SoftMin.Z_fderiv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:11:53.353322+00:00
-- url     : https://prove2.me/theorems/5dbfa80b-a450-4c14-b1e2-d81e35ed185f
-- title:
--   Derivative of the soft-minimum partition function
-- statement:
--   For finitely many vectors $v_i$ in a real inner product space, let $Z(x)=\sum_ie^{-\langle v_i,x\rangle}$, with weights $w_i=e^{-\langle v_i,x\rangle}/Z$ and $\nabla(x)=\sum_iw_i(x)\,v_i$. Then $Z$ is differentiable with
--   $$
--   DZ(x)=-Z(x)\,\bigl\langle\nabla(x),\cdot\bigr\rangle .
--   $$
--
--   Consequently $-\log Z$ has gradient $\nabla$, the weighted average of the $v_i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/SoftMinimum.lean#L62-L76

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.SoftMin
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
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem OAI.GaussianPropeller.SoftMin.Z_fderiv (v : ι → E) (x : E) :
    HasFDerivAt (Z v) (-(Z v x) • innerSL ℝ (grad v x)) x := by sorry
