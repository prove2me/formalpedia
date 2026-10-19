-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_SoftMin_hess_bound
-- name    : OAI.GaussianPropeller.SoftMin.hess_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:13:21.672679+00:00
-- url     : https://prove2.me/theorems/05a7f5f8-0e63-42b0-bc66-4797181265d4
-- title:
--   Hessian bound for the soft minimum
-- statement:
--   For finitely many vectors $v_i$ with $|v_i|\le L$, the Hessian of the soft minimum $-\log\sum_ie^{-\langle v_i,x\rangle}$, which is $\sum_iw_i(x)\,v_i\otimes(\nabla(x)-v_i)$, satisfies at every point
--   $$
--   \|\nabla^2(-\log Z)(x)\|\le2L^2 .
--   $$
--
--   The bound is uniform in $x$, which is what the heat-flow argument requires.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/SoftMinimum.lean#L112-L126

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

theorem OAI.GaussianPropeller.SoftMin.hess_bound (v : ι → E) {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ i, ‖v i‖ ≤ L) (x : E) :
    ‖hess v x‖ ≤ 2*L^2 := by sorry
