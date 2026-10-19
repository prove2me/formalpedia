-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_append_empty_partition
-- name    : OAI.GaussianPropeller.Reduction.append_empty_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:28:30.166128+00:00
-- url     : https://prove2.me/theorems/7c12d6d2-98ab-4adf-8b3e-3cd1a9c65c23
-- title:
--   Appending an empty cell preserves a partition
-- statement:
--   Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. A partition into $k$ cells is a family of measurable sets $A_1,\dots,A_k$ such that almost every point lies in exactly one of them. The centroid of $A$ is $z(A)=\int_Ax\,d\gamma_d$, and the value of the partition is $V=\sum_i|z(A_i)|^2$. A minimal optimal partition maximizes $V$ and, among maximizers, has the fewest cells of positive measure. If $A_1,\dots,A_k$ is a partition, then so is the family of $k+1$ sets obtained by appending the empty set:
--   $$
--   (A_1,\dots,A_k,\varnothing).
--   $$
--
--   Since the empty cell has centroid $0$, the value is unchanged, so the bound for $k$ cells transfers to more cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Attainment.lean#L292-L308

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
universe uE
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
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem OAI.GaussianPropeller.Reduction.append_empty_partition {d k : ℕ} {A : Fin k → Set (Space d)}
    (hA : IsPartition A) : IsPartition (Fin.lastCases ∅ A) := by sorry
