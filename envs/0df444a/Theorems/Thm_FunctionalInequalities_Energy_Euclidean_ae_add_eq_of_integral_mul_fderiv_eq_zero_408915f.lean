-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_ae_add_eq_of_integral_mul_fderiv_eq_zero_408915f
-- name    : FunctionalInequalities.Energy.Euclidean.ae_add_eq_of_integral_mul_fderiv_eq_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:56.684377+00:00
-- url     : https://prove2.me/theorems/dac5dc32-f078-4f70-8856-73c1c253b8f0
-- title:
--   Translation Invariance From Vanishing Weak Derivatives
-- statement:
--   This is a distributional translation-invariance statement for a locally integrable function.
--
--   Let $V$ be a finite-dimensional real inner-product normed additive group equipped with its Borel measurable structure and a second-countable topology. Let $m$ be an additive Haar measure on $V$, and let $h:V\to\mathbb R$ be locally integrable with respect to $m$. Assume that for every smooth compactly supported test function $\varphi:V\to\mathbb R$ and every direction $w\in V$,
--
--   $$
--   \int h(x)\,D\varphi(x)[w]\,dm(x)=0.
--   $$
--
--   Then, for every translation vector $v\in V$, $h$ is invariant under translation by $v$ almost everywhere:
--
--   $$
--   \forall v\in V,\qquad h(x+v)=h(x)\quad\text{for $m$-almost every }x.
--   $$
--
--   The Lean declaration is `ae_add_eq_of_integral_mul_fderiv_eq_zero`; the values are real, and the conclusion is an a.e. equality for each fixed translation vector. This is an auxiliary weak-gradient result and does not itself assert that $h$ is almost everywhere constant.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L276-L328 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.ae_add_eq_of_integral_mul_fderiv_eq_zero`; the repository is private at upload time).

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

theorem FunctionalInequalities.Energy.Euclidean.ae_add_eq_of_integral_mul_fderiv_eq_zero_408915f {h : V → ℝ} (hh : LocallyIntegrable h m)
    (h0 : ∀ φ : V → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ w : V,
      ∫ x, h x * fderiv ℝ φ x w ∂m = 0)
    (v : V) :
    ∀ᵐ x ∂m, h (x + v) = h x := by sorry
