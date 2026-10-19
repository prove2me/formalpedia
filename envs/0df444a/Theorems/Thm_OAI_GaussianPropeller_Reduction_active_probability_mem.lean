-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_active_probability_mem
-- name    : OAI.GaussianPropeller.Reduction.active_probability_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:30:24.735991+00:00
-- url     : https://prove2.me/theorems/48bfe19e-a8c4-4ce7-a451-dc2d7b7ad809
-- title:
--   Active cells carry at most half of the mass
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $V=\sum_i|z(A_i)|^2$. A minimal optimal partition maximizes $V$ and, among maximizers, has the fewest cells of positive measure. Let $A$ be a minimal optimal partition into $k\ge2$ cells with positive value, and let $\gamma_d(A_i)>0$. Then
--   $$
--   0<\gamma_d(A_i)\le\frac12 .
--   $$
--
--   This is the condition $P_j\le\frac12$ on the masses in a configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CellBounds.lean#L42-L65

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

theorem OAI.GaussianPropeller.Reduction.active_probability_mem (_hk : 2 ≤ k) {A : Fin k → Set (Space d)}
    (hA : MinimalOptimal A) (hpos : 0 < value A) {i : Fin k}
    (hi : gaussian d (A i) ≠ 0) : 0 < (gaussian d).real (A i) ∧ (gaussian d).real (A i) ≤ 1/2 := by sorry
