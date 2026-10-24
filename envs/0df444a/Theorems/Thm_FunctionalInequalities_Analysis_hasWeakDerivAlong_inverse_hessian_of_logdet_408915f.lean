-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_inverse_hessian_of_logdet_408915f
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:43.679157+00:00
-- url     : https://prove2.me/theorems/efbfb410-aae7-4c46-b666-65c2bea045a9
-- title:
--   Weak Derivative of the Inverse Hessian
-- statement:
--   Let $u,F:\mathbb{R}^n\to\mathbb{R}$, let $\nabla u$ be Lipschitz, let $F$ be Lipschitz, and assume that almost everywhere the Hessian $H_u$ is positive definite and
--
--   $$
--   \log\det H_u=F.
--   $$
--
--   Suppose a tensor $T$ gives locally $L^2$ weak directional derivatives of the entries of $H_u$. Then, for every coordinate direction $e_k$ and indices $i,j$, the inverse Hessian has weak derivative
--
--   $$
--   \partial_k(H_u^{-1})_{ij}
--   =-\bigl(H_u^{-1}T_kH_u^{-1}\bigr)_{ij},
--   $$
--
--   and this derivative is locally in $L^2$ on compact sets. The inverse-Hessian entries themselves are locally in $L^{\infty}$ on compact sets. This is a weak calculus statement and does not assume $C^2$ regularity.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1051-L1138 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_InverseHessian_Weak
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
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
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
section WeakInverseDerivative
open MeasureTheory Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_inverse_hessian_of_logdet_408915f {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} {G LF : NNReal}
    {T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ}
    (hG : LipschitzWith G (gradient u)) (hF : LipschitzWith LF F)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧ Real.log (hessianMatrix u x).det = F x)
    (hT : ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => T x k i j) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ k i j : Fin n,
      HasWeakDerivAlong (fun x => (hessianMatrix u x)⁻¹ i j)
        (fun x => -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j))
        (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
      (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
