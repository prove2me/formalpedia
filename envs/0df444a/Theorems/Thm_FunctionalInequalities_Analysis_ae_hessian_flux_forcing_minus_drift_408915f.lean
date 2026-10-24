-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_hessian_flux_forcing_minus_drift_408915f
-- name    : FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:52.861578+00:00
-- url     : https://prove2.me/theorems/a077b1ba-6e11-4b85-b552-acddbeb9c599
-- title:
--   Almost-Everywhere Hessian Flux Forcing Decomposition
-- statement:
--   This is a private almost-everywhere algebraic identity associated with the weak second Hessian evolution.
--
--   Let $u,W:\mathbb R^n\to\mathbb R$ be such that $u$ is $C^1$ with Lipschitz gradient, $W$ is $C^2$, and $-u+W\circ\nabla u$ is Lipschitz. Assume
--   $$
--   \det\nabla^2u(x)=\exp\bigl(-u(x)+W(\nabla u(x))\bigr)
--   $$
--   a.e. Assume a weak Hessian tensor $T$ and weak inverse-Hessian derivatives with the compact-local $L^2$ and `ENNReal`-valued local $L^\infty$ hypotheses stated in the declaration.
--
--   With
--   $$
--   R=(\nabla^2u)^{-1},\quad D_{kba}=-(RT_kR)_{ba},\quad
--   J_{ija}=\sum_bR_{ba}T_{bij},
--   $$
--   and
--   $$
--   Q_{ij}=-(\nabla^2u)_{ji}+\sum_a\left(T_{jia}\,\partial_aW(\nabla u)
--   +(\nabla^2u)_{ia}\sum_b(\nabla^2u)_{jb}(\nabla^2W)_{ba}(\nabla u)\right),
--   $$
--   the following equality holds for almost every $x$, simultaneously for all $i,j$:
--
--   $$
--   Q_{ij}-\sum_{a,b}T_{iab}D_{jba}
--   +\sum_bT_{bij}\sum_aD_{aba}
--   -\sum_aJ_{ija}\,\partial_a u
--   =
--   -(\nabla^2u)_{ij}
--   +(\nabla^2u\,\nabla^2W(\nabla u)\,\nabla^2u)_{ij}
--   +\operatorname{tr}(RT_iRT_j).
--   $$
--
--   This private lemma identifies the forcing term needed to convert the unweighted weak flux identity into the weighted curvature–Gram identity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L1198-L1280 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution.0.FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift`; the repository is private at upload time).

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
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Analysis.ae_hessian_flux_forcing_minus_drift_408915f {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    (hu : ContDiff ℝ 1 u)
    (hG : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (hF : LipschitzWith LF (fun x => -u x + W (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv : ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
          (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
            (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let Q := fun x i j => -hessianMatrix u x j i + ∑ a : Fin n,
      (T x j i a * fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a) +
        hessianMatrix u x i a * ∑ b : Fin n, hessianMatrix u x j b *
          hessianMatrix W (gradient u x) b a)
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j : Fin n,
      Q x i j - (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
        (∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)) -
        (∑ a : Fin n, J x i j a * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ a)) =
      -hessianMatrix u x i j +
        (hessianMatrix u x * hessianMatrix W (gradient u x) * hessianMatrix u x) i j +
        (R x * (Matrix.of fun a b => T x i a b) * R x *
          (Matrix.of fun a b => T x j a b)).trace := by sorry
