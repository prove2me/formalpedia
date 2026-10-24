-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Stein_norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f
-- name    : FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:18:09.01563+00:00
-- url     : https://prove2.me/theorems/19570eb9-347b-47ea-b6b8-b34cfeb2fe9b
-- title:
--   Coordinatewise Hessian Bound from Gradient Lipschitzness
-- statement:
--   This declaration gives a coordinatewise weak-Hessian estimate and is listed as partially related to the Key moment-map Hessian bound, Theorem 2.5 of Letwin2026.
--
--   Let $n$ be a natural number, let $u : \mathbb{R}^n \to \mathbb{R}$ be represented by `EuclideanSpace ℝ (Fin n)`, and let $G$ be a nonnegative real number represented by `NNReal`. Assume that the gradient map $\nabla u$ is $G$-Lipschitz with respect to the Euclidean norm. Then, for every point $x \in \operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}(n))$ and every pair of coordinate indices $i,j \in \operatorname{Fin}(n)$, the corresponding entry of `hessianMatrix u x` satisfies
--
--   $$
--   \left\|\operatorname{hessianMatrix}(u,x,i,j)\right\| \leq G.
--   $$
--
--   Here the norm on the real-valued Hessian entry is the usual absolute-value norm, and $G$ on the right-hand side denotes the coercion from `NNReal` to $\mathbb{R}$. This is a technical coordinatewise estimate that can be reused whenever a weak Hessian is defined through the derivative of a Lipschitz gradient.
--
--   **Formalization Note** The statement applies in finite-dimensional Euclidean space for every natural number $n$, including $n=0$, and does not assert classical $C^2$ regularity or differentiability everywhere. The Hessian coordinates are expressed using the Lean definition `hessianMatrix`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L400-L420 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, declaration `FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient`; the repository is private at upload time).

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
noncomputable section HessianEntryBounds
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
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

theorem FunctionalInequalities.Probability.Stein.norm_hessianMatrix_entry_le_of_lipschitz_gradient_408915f {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ‖hessianMatrix u x i j‖ ≤ (G : ℝ) := by sorry
