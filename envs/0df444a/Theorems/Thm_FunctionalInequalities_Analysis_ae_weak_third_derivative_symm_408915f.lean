-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_third_derivative_symm_408915f
-- name    : FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:04.596844+00:00
-- url     : https://prove2.me/theorems/adaab418-ca46-46cb-819c-733c10fb0fd9
-- title:
--   Almost-Everywhere Symmetry of Weak Third Derivatives
-- statement:
--   This is a weak-coordinate symmetry statement for third derivatives.
--
--   Let $u:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$ be $C^1$ with Lipschitz gradient. Let $T(x,k,i,j)$ be such that, for every $k,i,j<n$, the function $T(\cdot,k,i,j)$ is a weak derivative along $e_k$ of the Hessian entry $H_{ij}=\operatorname{hessianMatrix}(u,\cdot)_{ij}$. Then, for almost every $x$, simultaneously for all $k,i,j$,
--
--   $$T(x,k,i,j)=T(x,i,k,j),
--   \qquad T(x,k,i,j)=T(x,k,j,i).$$
--
--   The first equality exchanges the derivative and first Hessian indices; the second expresses symmetry in the Hessian indices. The declaration `ae_weak_third_derivative_symm` is an almost-everywhere identification result and does not assert that a classical third derivative exists.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L157-L281 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, declaration `FunctionalInequalities.Analysis.ae_weak_third_derivative_symm`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
section WeakThirdDerivativeSymmetry
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.ae_weak_third_derivative_symm_408915f {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hT : ∀ k i j, HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ k i j, T x k i j = T x i k j ∧ T x k i j = T x k j i := by sorry
