-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_integral_inv_hessianMatrix_mul_fderiv_eq_408915f
-- name    : FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:25.26831+00:00
-- url     : https://prove2.me/theorems/f7ec5af6-f146-4d0f-a76e-34f08cc0c9f4
-- title:
--   Weak Divergence Identity for the Inverse Hessian
-- statement:
--   This is the weak inverse-Hessian divergence identity, supporting the inverse-Hessian integration-by-parts route.
--
--   Let $u,F:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$ and has Lipschitz gradient.
--   2. $F$ is Lipschitz.
--   3. Almost everywhere,
--      $$\det(\operatorname{hessianMatrix}(u,x))=e^{F(x)}.$$
--   4. $\psi$ is Lipschitz and compactly supported.
--
--   For every $i<n$,
--
--   $$\sum_{j<n}\int H(x)^{-1}_{ij}\,D\psi(x)e_j\,dx
--   =\sum_{j<n}\int H(x)^{-1}_{ij}\,DF(x)e_j\,\psi(x)\,dx,$$
--
--   where $H(x)=\operatorname{hessianMatrix}(u,x)$ and all integrals use Lebesgue measure. The statement does not assume pointwise positive definiteness of $H$; matrix inversion is the Lean matrix inverse and the determinant identity is only almost everywhere.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L913-L1015 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
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
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open Matrix
open FunctionalInequalities.Probability.Stein
section LN10AInverseHessianDivergence
open MeasureTheory Set Filter
open scoped Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.sum_integral_inv_hessianMatrix_mul_fderiv_eq_408915f {n : ℕ}
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) {LF : NNReal} (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {Lψ : NNReal} (hψ : LipschitzWith Lψ ψ)
    (hψc : HasCompactSupport ψ) (i : Fin n) :
    ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      ∑ j, ∫ x, (hessianMatrix u x)⁻¹ i j * fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ j) * ψ x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
