-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:48.777458+00:00
-- url     : https://prove2.me/theorems/1d5e2631-5a29-4fee-bb88-3442e67f5046
-- title:
--   Mean Hessian Identity for a Lipschitz Gradient
-- statement:
--   This formalizes the analytic part of Lemma 2.3 of Letwin (arXiv:2607.24164v1).
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\phi:E\to\mathbb R$. Assume:
--
--   1. $\phi$ is $C^1$.
--   2. For some $G\in[0,\infty)$, the gradient $\nabla\phi$ is $G$-Lipschitz.
--   3. $\phi$ is convex on $E$.
--   4. $e^{-\phi}$ is integrable with respect to volume measure and
--      $$\int_E e^{-\phi(x)}\,dx=1.$$
--   5. The gradient belongs to $L^2(\nu)$, where $\nu=\operatorname{volume}.\operatorname{tilted}(-\phi)$.
--
--   Then, for all $u,v\in E$,
--   $$\int_E\left\langle D(\nabla\phi)(x)[u],v\right\rangle\,d\nu(x)=\int_E D\phi(x)[u]D\phi(x)[v] \,d\nu(x).$$
--
--   This identity relates the mean derivative of the Lipschitz gradient to products of directional derivatives and is useful in tilted integration-by-parts calculations.
--
--   **Formalization Note.** The derivative of $\nabla\phi$ is the pointwise Fréchet derivative supplied by `fderiv`; the equality is integrated against the normalized tilted measure.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.3. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean#L24-L224 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.LipschitzHessian`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.BakryEmery.integral_inner_fderiv_gradient_tilted_eq_integral_fderiv_mul_408915f (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ) {G : NNReal} (hG : LipschitzWith G (gradient φ))
    (hc : ConvexOn ℝ Set.univ φ)
    (hexp : Integrable (fun x => Real.exp (-φ x)) (volume : Measure E))
    (hnorm : ∫ x, Real.exp (-φ x) ∂(volume : Measure E) = 1)
    (hgrad : MemLp (gradient φ) 2 ((volume : Measure E).tilted (-φ))) (u v : E) :
    (∫ x, ⟪fderiv ℝ (gradient φ) x u, v⟫ ∂((volume : Measure E).tilted (-φ))) =
      ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂((volume : Measure E).tilted (-φ)) := by sorry
