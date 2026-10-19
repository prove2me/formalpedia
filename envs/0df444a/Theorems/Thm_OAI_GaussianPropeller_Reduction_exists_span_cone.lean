-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_exists_span_cone
-- name    : OAI.GaussianPropeller.Reduction.exists_span_cone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:48:43.320004+00:00
-- url     : https://prove2.me/theorems/451f0694-4ffe-497a-8ed4-08bb788d1c5c
-- title:
--   Transporting a cell to the span of the centroids
-- statement:
--   Let $\gamma_m$ be the standard Gaussian measure on $\mathbb R^m$. Let $z_1,\dots,z_k\in\mathbb R^d$ sum to zero and be pairwise obtuse, with $k-1=n+1$. Let $z_i\ne0$ and suppose the closed cell $\{x:\langle z_j,x\rangle\le\langle z_i,x\rangle\ \forall j\}$ has centroid $z_i$. Then there is a measurable cone $K\subseteq\mathbb R^{n+1}$ with
--   $$
--   \gamma_{n+1}(K)=\gamma_d(\text{cell}),\qquad \int_Kx_0\,d\gamma_{n+1}=|z_i| .
--   $$
--
--   So cell estimates in dimension $n+1=k-1$ apply to cells of any dimension $d$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapReduction.lean#L61-L114

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
open Coords
variable {d k n : ℕ} [NeZero k]

theorem OAI.GaussianPropeller.Reduction.exists_span_cone {z : Fin k → Space d} (hsum : ∑ j,z j=0)
    (hneg : Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hzi:z i≠0)
    (hdim : k-1=n+1) (hcen : centroid (closedCell z i)=z i) :
    ∃ K : Set (Space (n+1)), MeasurableSet K ∧
      (∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) ∧
      (gaussian (n+1)).real K=(gaussian d).real (closedCell z i) ∧
      (∫ x, K.indicator (fun x : Space (n+1)=> x 0) x ∂gaussian (n+1))=‖z i‖ := by sorry
