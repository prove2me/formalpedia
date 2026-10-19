-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_gaussian_hyperplane_null
-- name    : OAI.GaussianPropeller.Reduction.gaussian_hyperplane_null
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:56:56.495098+00:00
-- url     : https://prove2.me/theorems/eff89f17-9fa9-4726-b527-804433a358fc
-- title:
--   Gaussian measure of an affine hyperplane is zero
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$, $z\ne0$ a vector and $c\in\mathbb R$. Then
--   $$
--   \gamma_d\bigl(\{x:\langle z,x\rangle=c\}\bigr)=0 .
--   $$
--
--   Boundaries between score cells are therefore negligible, so ties in $\max_i\langle z_i,x\rangle$ happen almost never.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Dual.lean#L500-L521

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem OAI.GaussianPropeller.Reduction.gaussian_hyperplane_null (z : Space d) (hz : z ≠ 0) (c : ℝ) :
    gaussian d {x | ⟪z, x⟫ = c} = 0 := by sorry
