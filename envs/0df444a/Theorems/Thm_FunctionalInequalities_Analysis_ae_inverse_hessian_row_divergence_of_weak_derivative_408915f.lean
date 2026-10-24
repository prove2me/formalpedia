-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_inverse_hessian_row_divergence_of_weak_derivative_408915f
-- name    : FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:22.72919+00:00
-- url     : https://prove2.me/theorems/3c60d6b7-8508-4e0a-886f-39bb62b8da56
-- title:
--   Weak Inverse-Hessian Row Divergence
-- statement:
--   This formalizes a supporting weak inverse-Hessian identity, cited as a partial formalization of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $u,F:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$ with Lipschitz gradient, $F$ is Lipschitz, and almost everywhere $\det H=e^F$, where $H=\operatorname{hessianMatrix}(u,\cdot)$.
--   2. A tensor $T(x,k,a,b)$ is supplied together with weak directional derivatives of each entry $H(x)^{-1}_{ij}$, namely the derivative along $e_k$ is
--      $$-\bigl(H(x)^{-1}T(x,k)H(x)^{-1}\bigr)_{ij}.$$
--   3. These weak derivatives and inverse entries have the stated local $L^2$ and local $L^\infty$ (`ENNReal` exponent $\top$) membership on every compact set.
--
--   Then, for every row $b$, the vector field
--   $$x\mapsto\sum_a H(x)^{-1}_{ba}\,DF(x)e_a$$
--   belongs to $L^2$ on every compact set, and almost everywhere
--
--   $$\sum_a-\bigl(H(x)^{-1}T(x,a)H(x)^{-1}\bigr)_{ba}
--   =-\sum_a H(x)^{-1}_{ba}\,DF(x)e_a.$$
--
--   The declaration `ae_inverse_hessian_row_divergence_of_weak_derivative` is an interface theorem for a fixed weak inverse-derivative object; it does not construct $T$.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L1190-L1303 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative`; the repository is private at upload time).

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
section WeakInverseRowDivergence
open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.ae_inverse_hessian_row_divergence_of_weak_derivative_408915f {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hC1 : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hInv : ∀ k i j : Fin n,
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
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    ∀ b : Fin n,
      (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp
          (fun x => ∑ a : Fin n, (hessianMatrix u x)⁻¹ b a *
            fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a))
          2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (∑ a : Fin n, -(((hessianMatrix u x)⁻¹ *
          (Matrix.of fun c d => T x a c d) * (hessianMatrix u x)⁻¹) b a)) =
        -(∑ a : Fin n, (hessianMatrix u x)⁻¹ b a *
          fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ a)) := by sorry
