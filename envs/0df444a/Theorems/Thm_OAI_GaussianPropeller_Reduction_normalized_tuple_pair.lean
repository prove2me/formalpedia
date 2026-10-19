-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_normalized_tuple_pair
-- name    : OAI.GaussianPropeller.Reduction.normalized_tuple_pair
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T06:50:33.482196+00:00
-- url     : https://prove2.me/theorems/7816cc79-ac9b-4e3f-8750-218f4794e3ea
-- title:
--   The pair inequality for normalized centroids
-- statement:
--   Let $A$ be a minimal optimal Gaussian partition of $\mathbb R^d$ whose cells all have positive measure, with value $V>9/(8\pi)$. Let $z_j=z(A_j)/\sqrt V$ be the normalized centroids. For $z\ne0$ and $y$, the residual of $y$ along $z$ is $y+c\,z$ with coefficient $c=-\langle z,y\rangle/|z|^2$, the component of $y$ orthogonal to $z$. For $i\ne j$ and $i\ne l$, let $u,v$ be the residuals of $z_j,z_l$ along $z_i$, and $a,b$ the coefficients. Then
--   $$
--   |u|^2|v|^2-\langle u,v\rangle^2\le\Bigl(\frac3\pi\Bigr)^2|z_i|^2(1+a)^2(1+b)^2 .
--   $$
--
--   This is the pair condition of a configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/FourReduction.lean#L86-L110

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
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
variable {d k : ℕ}

theorem OAI.GaussianPropeller.Reduction.normalized_tuple_pair [NeZero k] {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hC:9/(8*Real.pi)<value A) (hall:∀ j,gaussian d (A j)≠0)
    {i j l:Fin k} (hij:i≠j) (hil:i≠l) :
    let z := fun j=>(Real.sqrt (value A))⁻¹•centroid (A j)
    let u := residualVector (z i) (z j)
    let v := residualVector (z i) (z l)
    ‖u‖^2*‖v‖^2-⟪u,v⟫^2 ≤ (3/Real.pi)^2*‖z i‖^2*
      (1+residualCoefficient (z i) (z j))^2*(1+residualCoefficient (z i) (z l))^2 := by sorry
