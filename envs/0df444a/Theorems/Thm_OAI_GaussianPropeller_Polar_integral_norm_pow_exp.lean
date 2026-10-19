-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Polar_integral_norm_pow_exp
-- name    : OAI.GaussianPropeller.Polar.integral_norm_pow_exp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:39:56.687991+00:00
-- url     : https://prove2.me/theorems/8170af55-efcb-4bbf-951a-af9b9b2e30dc
-- title:
--   Gaussian moments of radial exponential weights
-- statement:
--   Let $E=\mathbb R^\iota$ with $n=|\iota|$, let $\gamma$ be its standard Gaussian measure and $\sigma$ the surface measure on the unit sphere $S$ induced by Lebesgue measure. For $n\in\mathbb N$ and $b>0$ let $R(n,b)=\int_0^\infty r^ne^{-br^2}\,dr$ be the radial Gaussian integral. For $q\in\mathbb N$ and $a\ge0$,
--   $$
--   \int|x|^q\,e^{-a|x|^2}\,d\gamma(x)=\frac{R\bigl(n-1+q,\ a+\frac12\bigr)}{R\bigl(n-1,\ \frac12\bigr)} .
--   $$
--
--   This evaluates the Gaussian averages that appear in cap estimates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Polar.lean#L226-L239

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Polar
universe uι
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
open Real
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => Metric.sphere (0:E) 1

theorem OAI.GaussianPropeller.Polar.integral_norm_pow_exp (q : ℕ) {a : ℝ} (_ha : 0≤a) :
    ∫ x : E, ‖x‖^q*exp (-a*‖x‖^2) ∂stdGaussian E =
      radial (Fintype.card ι-1+q) (a+1/2)/radial (Fintype.card ι-1) (1/2) := by sorry
