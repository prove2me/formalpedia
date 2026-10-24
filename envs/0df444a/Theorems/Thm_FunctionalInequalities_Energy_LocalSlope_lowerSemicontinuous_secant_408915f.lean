-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_lowerSemicontinuous_secant_408915f
-- name    : FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:16.073573+00:00
-- url     : https://prove2.me/theorems/0000e233-7c92-4bb4-9554-18e1da96082c
-- title:
--   Lower Semicontinuity Of The Secant Supremum
-- statement:
--   This lemma establishes lower semicontinuity of each fixed-radius secant supremum.
--
--   Let $X$ be a metric space, let $f:X\to\mathbb R$ be continuous, and let $r\in\mathbb R$. Define `secant f r` at $x$ as the supremum, over points $y$ with $d(y,x)<r$, of the extended quotient
--
--   $$
--   \operatorname{ENNReal.ofReal}\!\left(\frac{d(f(y),f(x))}{d(y,x)}\right).
--   $$
--
--   Then the map $x\mapsto\operatorname{secant}(f,r)(x)$ is lower semicontinuous:
--
--   $$
--   \operatorname{LowerSemicontinuous}\bigl(\operatorname{secant}(f,r)\bigr).
--   $$
--
--   The Lean declaration is `lowerSemicontinuous_secant`. The secant values are `ENNReal` values, so the conclusion allows the value $\top$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean#L63-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Density`, declaration `FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_LocalSlope_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
universe u
section
namespace FunctionalInequalities.Energy.LocalSlope
end FunctionalInequalities.Energy.LocalSlope
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.LocalSlope
section Measurability
variable {X : Type*} [MetricSpace X]

theorem FunctionalInequalities.Energy.LocalSlope.lowerSemicontinuous_secant_408915f {f : X → ℝ} (hf : Continuous f) (r : ℝ) :
    LowerSemicontinuous (secant f r) := by sorry
