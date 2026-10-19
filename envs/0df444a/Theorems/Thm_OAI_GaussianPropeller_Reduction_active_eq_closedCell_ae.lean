-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_active_eq_closedCell_ae
-- name    : OAI.GaussianPropeller.Reduction.active_eq_closedCell_ae
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:57:26.489835+00:00
-- url     : https://prove2.me/theorems/de65fcff-d581-424b-8f80-93b62bc2b7a6
-- title:
--   Active cells of a minimal optimal partition are Voronoi cones
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $\sum_i|z(A_i)|^2$. Let $A$ be a minimal optimal partition: optimal, and with the fewest cells of positive measure among optimal partitions. Assume its value is positive, and let $\gamma_d(A_i)>0$. Then, up to a $\gamma_d$-null set,
--   $$
--   A_i=\bigl\{x:\ \langle z(A_j),x\rangle\le\langle z(A_i),x\rangle\ \text{for all }j\bigr\}.
--   $$
--
--   Each cell of positive mass is the closed polyhedral cone on which its own centroid scores highest.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Dual.lean#L534-L564

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.active_eq_closedCell_ae {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) :
    A i =ᵐ[gaussian d] closedCell (fun j => centroid (A j)) i := by sorry
