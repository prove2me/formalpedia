-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_408915f
-- name    : FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:37.801719+00:00
-- url     : https://prove2.me/theorems/ffef2f2d-f0a1-45ec-a244-110223eab13f
-- title:
--   Gradient Second Moments Under an Isotropic Pushforward
-- statement:
--   This formalizes the second-moment identity in Lemma 2.3 of Letwin (arXiv:2607.24164v1).
--
--   Let $\nu$ be a probability measure on a finite-dimensional real inner-product space, let $\phi:E\to\mathbb{R}$, and assume `gradient φ` is measurable. If the pushforward $(\nabla\phi)_*\nu$ is isotropic, then for every $u,v\in E$,
--
--   $$
--   \int D\phi(x)[u]D\phi(x)[v]\\,d\nu(x)=\langle u,v\rangle.
--   $$
--
--   The conclusion uses the isotropy of the pushforward only; no convexity or regularity of $\phi$ beyond the stated measurable gradient representation is assumed.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.3. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/Isotropic.lean#L143-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.Isotropic`, declaration `FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.integral_fderiv_mul_fderiv_eq_inner_of_isotropic_map_408915f
    (ν : ProbabilityMeasure E) {φ : E → ℝ} (hφ : Measurable (gradient φ))
    (hiso : Isotropic (ν.map hφ.aemeasurable)) (u v : E) :
    ∫ x, fderiv ℝ φ x u * fderiv ℝ φ x v ∂(ν : Measure E) = ⟪u, v⟫ := by sorry
