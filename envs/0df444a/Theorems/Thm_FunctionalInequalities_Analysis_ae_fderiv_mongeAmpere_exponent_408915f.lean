-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_fderiv_mongeAmpere_exponent_408915f
-- name    : FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:29.575734+00:00
-- url     : https://prove2.me/theorems/f78cd98c-05eb-481d-9ac6-f2d1e1831628
-- title:
--   Almost-Everywhere Derivative of the Monge–Ampère Exponent
-- statement:
--   This formalizes the coordinate chain-rule identity associated with the Monge–Ampère exponent, cited as a partial formalization of Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb N$ and let $u,V:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$.
--   2. Its gradient is Lipschitz with some constant $G\in[0,\infty)$.
--   3. $V$ is $C^1$.
--
--   Then, for almost every $x$ and every coordinate index $j<n$,
--
--   $$D\bigl[-u+V\circ\nabla u\bigr](x)e_j
--   =-Du(x)e_j+\sum_{k<n}H_u(x)_{jk}\,DV(\nabla u(x))e_k,$$
--
--   where $H_u$ is the coordinate matrix `hessianMatrix`, and $e_j$ is `EuclideanSpace.basisFun (Fin n) ℝ j`. The declaration is a coordinate identity only; it does not assert a Monge–Ampère equation.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean#L218-L296 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Weak`, declaration `FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent`; the repository is private at upload time).

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
section MongeAmpereExponentDerivative
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent_408915f {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          ∑ k, hessianMatrix u x j k *
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by sorry
