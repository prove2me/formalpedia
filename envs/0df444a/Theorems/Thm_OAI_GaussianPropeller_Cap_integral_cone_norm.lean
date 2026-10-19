-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Cap_integral_cone_norm
-- name    : OAI.GaussianPropeller.Cap.integral_cone_norm
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T06:43:09.137453+00:00
-- url     : https://prove2.me/theorems/74fbd55e-aff7-4be2-b557-2e31f43715f8
-- title:
--   Gaussian first moment of the norm on a cone
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $\mathbb R^d$ with $d>0$, and $R(n,b)=\int_0^\infty r^ne^{-br^2}dr$. A set $K$ is a cone if $rx\in K\iff x\in K$ for all $r>0$. For every measurable cone $K$,
--   $$
--   \int_K|x|\,d\gamma(x)=\frac{R\bigl(d,\frac12\bigr)}{R\bigl(d-1,\frac12\bigr)}\,\gamma(K).
--   $$
--
--   On cones, the norm has the same average as on the whole space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/CapBounds.lean#L96-L122

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
open Coords OneCell ProbabilityBounds Polar
open scoped Topology
variable {n : ℕ}

theorem OAI.GaussianPropeller.Cap.integral_cone_norm {d : ℕ} (hd : 0<d) (K : Set (CE d))
    (hK : MeasurableSet K) (hcone : ∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) :
    (∫ x : CE d, K.indicator (fun x => ‖x‖) x ∂stdGaussian (CE d)) =
      radial d (1/2)/radial (d-1) (1/2) * (stdGaussian (CE d)).real K := by sorry
