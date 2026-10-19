-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Cap_cone_three
-- name    : OAI.GaussianPropeller.Cap.cone_three
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:44:16.440394+00:00
-- url     : https://prove2.me/theorems/54a86f28-92e1-41e3-8d68-e25407ac2f04
-- title:
--   First moment bound for cones in three dimensions
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $\mathbb R^3$. A set $K$ is a cone if $rx\in K\iff x\in K$ for all $r>0$. Let $K$ be a measurable cone with $0<\gamma(K)<1$ and $\gamma(K)\le\frac12$. Then, writing $P=\gamma(K)$,
--   $$
--   \int_Kx_0\,d\gamma\le\frac4{\sqrt{2\pi}}\,P\,(1-P).
--   $$
--
--   For four cells this gives the cap $|z_j|\le\frac83P_j(1-P_j)$ on the normalized centroids of a configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapBounds.lean#L199-L217

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Cap
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
open OneCell ProbabilityBounds Polar

theorem OAI.GaussianPropeller.Cap.cone_three (K : Set (CE 3)) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K)
    (hP : (stdGaussian (CE 3)).real K ∈ Ioo (0:ℝ) 1)
    (hPh : (stdGaussian (CE 3)).real K ≤ 1/2) :
    (∫ x : CE 3, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 3)) ≤
      4*gaussianConst*(stdGaussian (CE 3)).real K*(1-(stdGaussian (CE 3)).real K) := by sorry
