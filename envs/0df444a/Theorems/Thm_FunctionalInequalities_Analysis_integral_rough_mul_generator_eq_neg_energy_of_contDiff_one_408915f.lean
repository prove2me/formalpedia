-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_408915f
-- name    : FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:25:06.006534+00:00
-- url     : https://prove2.me/theorems/7f84c0f6-b11b-43ff-bfe1-74930419d09b
-- title:
--   Rough Inverse-Hessian Generator–Energy Identity
-- statement:
--   This is a rough weak-test version of the inverse-Hessian generator identity associated with Lemma A.5 of Letwin (arXiv:2607.24164v1), locator Lemma A.5.
--
--   Let $u,V,\chi:\mathbb R^n\to\mathbb R$ be $C^1$, with $u$ having Lipschitz gradient and $\chi$ having Lipschitz gradient and compact support. Assume $-u+V\circ\nabla u$ is Lipschitz and
--   $$
--   \det\nabla^2u=\exp(-u+V(\nabla u))
--   $$
--   a.e. Assume compact-local `ENNReal` $L^\infty$ bounds for the entries of $(\nabla^2u)^{-1}$ and integrability of
--   $$
--   \left(\operatorname{tr}((\nabla^2u)^{-1}\nabla^2\chi)
--   -\nabla V(\nabla u)\cdot\nabla\chi\right)e^{-u}.
--   $$
--   Let $\eta$ be locally integrable and bounded by $C$, and let $a_i$ be its weak coordinate derivatives, compact-locally in $L^2$.
--
--   Then both displayed pairings are integrable and
--
--   $$
--   \int \eta(x)\left(\operatorname{tr}((\nabla^2u(x))^{-1}\nabla^2\chi(x))
--   -\nabla V(\nabla u(x))\cdot\nabla\chi(x)\right)e^{-u(x)}\,dx
--   $$
--   $$
--   =-\int\left(\sum_{i,j}(\nabla^2u(x))^{-1}_{ij}a_i(x)\partial_j\chi(x)\right)e^{-u(x)}\,dx.
--   $$
--
--   This is the rough testing interface used for bounded weak functions against height cutoffs.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L912-L1009 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, declaration `FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
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
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact

noncomputable section
open MeasureTheory Filter Set Metric Matrix
open FunctionalInequalities.Probability.Stein
open scoped ContDiff Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.integral_rough_mul_generator_eq_neg_energy_of_contDiff_one_408915f {n : ℕ}
    {u V χ η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) {LF : NNReal}
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hχ : ContDiff ℝ 1 χ) {Gχ : NNReal} (hGχ : LipschitzWith Gχ (gradient χ))
    (hχc : HasCompactSupport χ)
    (hInv : ∀ i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hForce : Integrable (fun x =>
      (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    {C : ℝ} (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    Integrable (fun x => η x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
        fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
      a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix χ x).trace -
      fderiv ℝ V (gradient u x) (gradient χ x)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
    -(∫ x, (∑ i : Fin n, ∑ j : Fin n, (hessianMatrix u x)⁻¹ i j *
      a i x * fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
