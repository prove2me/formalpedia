-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_sum_inv_gradient_test_sub_chain_eq_408915f
-- name    : FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:18:27.114973+00:00
-- url     : https://prove2.me/theorems/cee95045-2f3b-4ea4-891d-cd614a875733
-- title:
--   Finite Inverse-Hessian Cancellation Identity
-- statement:
--   This is a finite-dimensional algebraic identity supporting the weak inverse-Hessian calculation.
--
--   Let $A,B$ be real $n\times n$ matrices. Assume $A$ is Hermitian and $\det A$ is a unit, so that $A^{-1}$ is available. For real $a$ and vectors $b,p,q,r:\operatorname{Fin}(n)\to\mathbb R$, the difference between the two displayed inverse-matrix contractions equals
--   $$\sum_{i,j}(A^{-1})_{ij}b_i r_j
--   +a\left(\operatorname{tr}(A^{-1}B)-\sum_iq_i r_i\right).$$
--
--   More explicitly, the left side is
--   $$\sum_{i,j}(A^{-1})_{ij}(b_jr_i-ap_jr_i+aB_{ji})
--   -\sum_{i,j}(A^{-1})_{ij}\left(-p_j+\sum_kA_{jk}q_k\right)(ar_i).$$
--
--   The lemma contains no analytic assumptions; it is a reusable matrix-and-finite-sum cancellation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L308-L369 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `_private.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak.0.FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq`; the repository is private at upload time).

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
section InverseMatrixCancellation
open scoped BigOperators
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.sum_inv_gradient_test_sub_chain_eq_408915f {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hdet : IsUnit A.det)
    (a : ℝ) (b p q r : Fin n → ℝ) :
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
      (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
      (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
        a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by sorry
