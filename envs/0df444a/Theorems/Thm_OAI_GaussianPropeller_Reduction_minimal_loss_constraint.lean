-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_minimal_loss_constraint
-- name    : OAI.GaussianPropeller.Reduction.minimal_loss_constraint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:31:05.178343+00:00
-- url     : https://prove2.me/theorems/144e0696-9e08-4c2e-aa96-8fcc983aa325
-- title:
--   The loss constraint on each cell of a counterexample
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $V=\sum_i|z(A_i)|^2$. A minimal optimal partition maximizes $V$ and, among maximizers, has the fewest cells of positive measure. Let $p(x)$ be the standard normal tail probability and $L(x)=p(x)^2\lambda(x)\bigl(\lambda(x)-x\bigr)$ the loss function, where $\lambda$ is the inverse Mills ratio. Let $A$ be a minimal optimal partition into $k\ge2$ cells of positive measure with $V>9/(8\pi)$. For a cell $i$, let $r=|z(A_i)|/\sqrt V$ be its normalized centroid length. There is $x\ge0$ with $p(x)=\gamma_d(A_i)$ and
--   $$
--   \frac{V\,r^2}{1+\sqrt{1-\frac k{k-1}r^2}}\le L(x).
--   $$
--
--   Together with the loss tests, this yields the linear and quadratic lower bounds on the masses in a configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CellBounds.lean#L96-L132

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
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
open Set GaussianPropeller.Quantile GaussianPropeller.OneCell GaussianPropeller.ProbabilityBounds
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.minimal_loss_constraint (hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hC : 9/(8*Real.pi) < value A)
    (hall : ∀ j, gaussian d (A j) ≠ 0) (i : Fin k) :
    ∃ x ≥ (0:ℝ), p x=(gaussian d).real (A i) ∧
      (value A)*(‖centroid (A i)‖/Real.sqrt (value A))^2 /
      (1+Real.sqrt (1-((k:ℝ)/((k:ℝ)-1))*(‖centroid (A i)‖/Real.sqrt (value A))^2)) ≤ loss x := by sorry
