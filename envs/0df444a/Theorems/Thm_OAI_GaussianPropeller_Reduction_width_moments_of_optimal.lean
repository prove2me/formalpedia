-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_width_moments_of_optimal
-- name    : OAI.GaussianPropeller.Reduction.width_moments_of_optimal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:56:21.698742+00:00
-- url     : https://prove2.me/theorems/71d4c7e3-ebe0-42ae-b408-5199e620ce7c
-- title:
--   Optimal partitions realize the width of their moments
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $\sum_i|z(A_i)|^2$. For $v=(v_1,\dots,v_k)\in(\mathbb R^d)^k$ the width is $w(v)=\int\max_i\langle v_i,x\rangle\,d\gamma_d(x)$, and the moment tuple of a partition is $m(A)=(z(A_1),\dots,z(A_k))$. A partition is optimal if its value is maximal among partitions into $k$ cells. If $A$ is optimal, then
--   $$
--   w\bigl(m(A)\bigr)=\sum_i|z(A_i)|^2 .
--   $$
--
--   So an optimal partition is, up to null sets, the score partition of its own centroids.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Dual.lean#L388-L401

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.width_moments_of_optimal {A : Fin k → Set (Space d)} (hA : Optimal A) :
    width (moments A) = value A := by sorry
