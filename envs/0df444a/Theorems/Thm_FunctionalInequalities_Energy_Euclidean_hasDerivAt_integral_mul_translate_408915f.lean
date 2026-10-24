-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_hasDerivAt_integral_mul_translate_408915f
-- name    : FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:55.808279+00:00
-- url     : https://prove2.me/theorems/3de576f0-940c-4cf7-8685-6da157539e0f
-- title:
--   Derivative of an Integral Against a Translated Test
-- statement:
--   This proves differentiation under the integral sign for translated test functions.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be a measure on $V$, and let $h:V\to\mathbb R$ be locally integrable with respect to $m$. Let $\phi:V\to\mathbb R$ be smooth and compactly supported. For $v\in V$ and $t\in\mathbb R$, define
--
--   $$
--   F(s)=\int h(x)\phi(x-sv)\,dm(x).
--   $$
--
--   Then $F$ has derivative at $t$ equal to
--
--   $$
--   F'(t)=-\int h(x)D\phi(x-tv)v\,dm(x).
--   $$
--
--   Equivalently,
--
--   $$
--   \operatorname{HasDerivAt}\!\left(s\mapsto\int h(x)\phi(x-sv)\,dm(x),
--   -\int h(x)D\phi(x-tv)v\,dm(x),t\right).
--   $$
--
--   This is a technical differentiation lemma used to convert a weak derivative condition into translation identities.
--
--   **Formalization Note** The declaration does not assume that $m$ is an additive Haar measure.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L86-L161 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.Euclidean.hasDerivAt_integral_mul_translate_408915f {h : V → ℝ} (hh : LocallyIntegrable h m) {φ : V → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ x, h x * φ (x - s • v) ∂m)
      (-∫ x, h x * fderiv ℝ φ (x - t • v) v ∂m) t := by sorry
