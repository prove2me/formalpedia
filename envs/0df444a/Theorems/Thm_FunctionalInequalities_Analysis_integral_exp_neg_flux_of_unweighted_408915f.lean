-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_exp_neg_flux_of_unweighted_408915f
-- name    : FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:59.795867+00:00
-- url     : https://prove2.me/theorems/31868db2-a202-4c02-89b7-c9206f0e6b2e
-- title:
--   Exponential Weighting of an Unweighted Flux Identity
-- statement:
--   This is a private weighted-testing lemma for compactly supported $C^1$ tests.
--
--   Let $u,c:\mathbb R^n\to\mathbb R$ be such that $u$ is $C^1$. Let $J_a$ be locally integrable for every coordinate $a$, and let $c$ be locally integrable. Assume that every compactly supported $C^1$ function $\phi$ satisfies
--
--   $$
--   \int\sum_aJ_a\,\partial_a\phi\,dx=-\int c\phi\,dx.
--   $$
--
--   Then $e^{-u}(c-\sum_aJ_a\partial_a u)$ is locally integrable, and every compactly supported $C^1$ function $\psi$ satisfies
--
--   $$
--   \int e^{-u}\sum_aJ_a\,\partial_a\psi\,dx
--   =-\int e^{-u}\left(c-\sum_aJ_a\partial_a u\right)\psi\,dx.
--   $$
--
--   The lemma is a private product-rule interface for passing from an unweighted divergence identity to its $e^{-u}$-weighted form.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1284-L1393 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution.0.FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Piola
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
section WeightedWeakHessianEvolution
open Matrix MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
open scoped ContDiff
open scoped BigOperators
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.integral_exp_neg_flux_of_unweighted_408915f {n : ℕ}
    {u c : EuclideanSpace ℝ (Fin n) → ℝ}
    {J : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
    (hu : ContDiff ℝ 1 u)
    (hJ : ∀ a : Fin n, LocallyIntegrable (fun x => J x a)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hc : LocallyIntegrable c (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ x, ∑ a : Fin n, J x a *
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ a)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, c x * φ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    LocallyIntegrable
      (fun x => Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, Real.exp (-u x) * (∑ a : Fin n, J x a *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, Real.exp (-u x) * (c x - ∑ a : Fin n, J x a *
        fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
