-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_integral_mul_sub_translate_eq_zero_408915f
-- name    : FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:55.833664+00:00
-- url     : https://prove2.me/theorems/736bfc80-53e5-4e1c-a582-e188751bb5f4
-- title:
--   Vanishing Integral Difference Under a Zero Weak Gradient
-- statement:
--   This derives a translation identity from a zero weak gradient.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $m$ be a measure on $V$, and let $h:V\to\mathbb R$ be locally integrable. Assume that for every smooth compactly supported test function $\psi$ and every direction $w\in V$,
--
--   $$
--   \int h(x)D\psi(x)w\,dm(x)=0.
--   $$
--
--   Then, for every smooth compactly supported $\phi$ and every $v\in V$,
--
--   $$
--   \int h(x)\bigl(\phi(x)-\phi(x-v)\bigr)\,dm(x)=0.
--   $$
--
--   The statement is an intermediate translation-invariance identity in the argument that a locally integrable function with zero weak gradient is almost everywhere constant.
--
--   **Formalization Note** The quantification over test functions includes the stated smoothness and compact-support hypotheses, and no Haar-measure assumption is required here.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L163-L248 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero`; the repository is private at upload time).

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

theorem FunctionalInequalities.Energy.Euclidean.integral_mul_sub_translate_eq_zero_408915f {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    {φ : V → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (v : V) :
    ∫ x, h x * (φ x - φ (x - v)) ∂m = 0 := by sorry
