-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Stein_chain_coordinate_of_differentiableAt_gradient_408915f
-- name    : FunctionalInequalities.Probability.Stein.chain_coordinate_of_differentiableAt_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:22:42.19468+00:00
-- url     : https://prove2.me/theorems/936cb955-5209-49d6-84cf-b9acc8b90f7a
-- title:
--   Coordinate Chain Rule Through the Gradient Map
-- statement:
--   This statement gives a coordinate chain rule for a composition with a gradient map.
--
--   Let $n\in\mathbb N$ and let $u,f:\mathbb R^n\to\mathbb R$ be $C^1$. At a point $y\in\mathbb R^n$, assume that $∇u$ is differentiable at $y$. For every coordinate $i\in\operatorname{Fin}(n)$,
--
--   $$
--   D_{e_i}(f\circ∇u)(y)
--   =
--   \sum_j (\nabla^2u(y))_{ij}\,(\nabla f(\nabla u(y)))_j.
--   $$
--
--   Here `hessianMatrix u y` is the matrix used for the weak Hessian coordinates. The result is a finite-dimensional pointwise identity and makes no global invertibility claim about $∇u$.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.7 (Fathi [29, Theorem 2.3]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L501-L535 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, declaration `FunctionalInequalities.Probability.Stein.chain_coordinate_of_differentiableAt_gradient`; the repository is private at upload time).

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
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff
section C1GradientChain
open MeasureTheory Matrix
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Stein
end FunctionalInequalities.Probability.Stein
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 400000

theorem FunctionalInequalities.Probability.Stein.chain_coordinate_of_differentiableAt_gradient_408915f {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (hf : ContDiff ℝ 1 f) {y : EuclideanSpace ℝ (Fin n)}
    (hy : DifferentiableAt ℝ (gradient u) y) (i : Fin n) :
    fderiv ℝ (f ∘ gradient u) y (EuclideanSpace.basisFun (Fin n) ℝ i) =
      ∑ j, hessianMatrix u y i j * gradient f (gradient u y) j := by sorry
