-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Cap_cone_four
-- name    : OAI.GaussianPropeller.Cap.cone_four
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T06:46:48.322189+00:00
-- url     : https://prove2.me/theorems/ca3565ec-ee42-4195-b48f-dd210b006798
-- title:
--   First moment bound for cones in four dimensions
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $\mathbb R^4$. A set $K$ is a cone if $rx\in K\iff x\in K$ for all $r>0$. Let $K$ be a measurable cone with $\gamma(K)>0$ and $M=\int_Kx_0\,d\gamma\ge0$. Then
--   $$
--   M^2\le0.3852\,\gamma(K).
--   $$
--
--   This sharpens the general one-cell bound $|z|^2\le0.405\,P$ for cells living in a four-dimensional span.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapNumeric.lean#L205-L270

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
open OneCell ProbabilityBounds Polar CapNumeric

theorem OAI.GaussianPropeller.Cap.cone_four (K : Set (CE 4)) (hK : MeasurableSet K)
    (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K)
    (hP : 0<(stdGaussian (CE 4)).real K)
    (hM0 : 0≤∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4)) :
    (∫ x : CE 4, K.indicator (fun x=>x 0) x ∂stdGaussian (CE 4))^2 ≤
      (963/2500:ℝ)*(stdGaussian (CE 4)).real K := by sorry
