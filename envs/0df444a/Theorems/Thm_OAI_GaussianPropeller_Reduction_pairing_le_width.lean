-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_pairing_le_width
-- name    : OAI.GaussianPropeller.Reduction.pairing_le_width
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:55:42.731701+00:00
-- url     : https://prove2.me/theorems/aaceb09d-df03-48e5-aadd-9979d477c5b4
-- title:
--   Moment pairings are bounded by the width
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $\sum_i|z(A_i)|^2$. For $v=(v_1,\dots,v_k)\in(\mathbb R^d)^k$ the width is $w(v)=\int\max_i\langle v_i,x\rangle\,d\gamma_d(x)$, and the moment tuple of a partition is $m(A)=(z(A_1),\dots,z(A_k))$. A partition is optimal if its value is maximal among partitions into $k$ cells. For every partition $A$ into $k$ cells and every $v\in(\mathbb R^d)^k$,
--   $$
--   \langle v,m(A)\rangle=\sum_i\langle v_i,z(A_i)\rangle\le w(v).
--   $$
--
--   This is the weak duality between partitions and score vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Dual.lean#L164-L178

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.pairing_le_width {A : Fin k → Set (Space d)} (hA : IsPartition A)
    (v : Tuple d k) : ⟪v, moments A⟫ ≤ width v := by sorry
