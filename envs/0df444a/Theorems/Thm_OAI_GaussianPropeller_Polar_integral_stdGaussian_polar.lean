-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Polar_integral_stdGaussian_polar
-- name    : OAI.GaussianPropeller.Polar.integral_stdGaussian_polar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:36:09.452999+00:00
-- url     : https://prove2.me/theorems/90b57469-09fe-4090-8601-53cebf0d7ae0
-- title:
--   Gaussian integrals in polar coordinates
-- statement:
--   Let $E=\mathbb R^\iota$ with $n=|\iota|$, let $\gamma$ be its standard Gaussian measure and $\sigma$ the surface measure on the unit sphere $S$ induced by Lebesgue measure. For every $f:E\to\mathbb R$,
--   $$
--   \int f\,d\gamma=(2\pi)^{-n/2}\int_S\int_0^\infty e^{-r^2/2}\,f(r\theta)\,r^{n-1}\,dr\,d\sigma(\theta).
--   $$
--
--   Gaussian integrals separate into a radial factor and an integral over directions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Polar.lean#L55-L74

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
open Translation
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "S" => sphere (0 : E) 1
local notation "V" => (volume : Measure E)

theorem OAI.GaussianPropeller.Polar.integral_stdGaussian_polar (f : E → ℝ) :
    ∫ x, f x ∂stdGaussian E = (Real.sqrt (2*Real.pi))⁻¹ ^ Fintype.card ι *
      ∫ p : S × Ioi (0 : ℝ), Real.exp (-p.2.1^2/2) * f (p.2.1 • p.1.1)
        ∂(V).toSphere.prod (Measure.volumeIoiPow (Fintype.card ι - 1)) := by sorry
