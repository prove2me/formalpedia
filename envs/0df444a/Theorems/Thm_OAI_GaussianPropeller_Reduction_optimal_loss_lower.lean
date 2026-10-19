-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_optimal_loss_lower
-- name    : OAI.GaussianPropeller.Reduction.optimal_loss_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:59:20.038842+00:00
-- url     : https://prove2.me/theorems/2aee5cf3-7131-44d4-b002-f7c2f666cf56
-- title:
--   A lower bound for the advantage of a cell in an optimal partition
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $\sum_i|z(A_i)|^2$. Let $A$ be an optimal partition into $k\ge2$ cells with value $V$, centroids $z_j=z(A_j)$, and fix $i$. Then
--   $$
--   V-\sqrt V\,\sqrt{V-\tfrac k{k-1}|z_i|^2}\ \le\ \int\Bigl(\langle z_i,x\rangle-\max_{j\ne i}\langle z_j,x\rangle\Bigr)_+\,d\gamma_d(x).
--   $$
--
--   The right side is the expected margin by which cell $i$ wins. A cell with a long centroid must win by a large margin, which is the input to all later estimates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Deletion.lean#L176-L198

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.optimal_loss_lower (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : Optimal A) (i : Fin k) :
    value A - Real.sqrt (value A) *
      Real.sqrt (value A - ((k:ℝ)/((k:ℝ)-1)) * ‖centroid (A i)‖^2) ≤
    ∫ x, max (⟪centroid (A i),x⟫ -
      omittedMax hk (fun j => centroid (A j)) i x) 0 ∂gaussian d := by sorry
