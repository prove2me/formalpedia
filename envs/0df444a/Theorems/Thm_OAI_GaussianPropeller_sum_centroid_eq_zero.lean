-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_sum_centroid_eq_zero
-- name    : OAI.GaussianPropeller.sum_centroid_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:52:28.380985+00:00
-- url     : https://prove2.me/theorems/7b4c8651-cc5a-4474-aec8-ebc245343005
-- title:
--   Centroids of a Gaussian partition sum to zero
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $\sum_i|z(A_i)|^2$. For every partition $A_1,\dots,A_k$ of $\mathbb R^d$,
--   $$
--   \sum_{i=1}^kz(A_i)=0 .
--   $$
--
--   The centroids of the cells always balance, because the standard Gaussian has mean zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Moments.lean#L47-L59

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments

open OAI OAI.GaussianPropeller
universe uF
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace

theorem OAI.GaussianPropeller.sum_centroid_eq_zero {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : ∑ i, centroid (A i) = 0 := by sorry
