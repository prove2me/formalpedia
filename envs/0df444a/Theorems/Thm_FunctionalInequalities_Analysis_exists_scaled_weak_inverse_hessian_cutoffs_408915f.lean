-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_scaled_weak_inverse_hessian_cutoffs_408915f
-- name    : FunctionalInequalities.Analysis.exists_scaled_weak_inverse_hessian_cutoffs_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:25:23.084766+00:00
-- url     : https://prove2.me/theorems/d18b2e33-e48e-4e34-8dfd-212d0d6bd16b
-- title:
--   Scaled Weak Inverse-Hessian Height Cutoffs
-- statement:
--   This is the weak $C^1$ cutoff construction associated with Lemma A.4 of Letwin (arXiv:2607.24164v1), and is used in the proof architecture surrounding Theorem 2.5.
--
--   Let $u,V:\mathbb R^n\to\mathbb R$ satisfy the stated $C^1$ regularity, Lipschitzness of $u$ and $\nabla u$, Lipschitzness of $-u+V\circ\nabla u$, the a.e. Monge–Ampère identity, and a.e. positive definiteness of $\nabla^2u$. Assume $u$ is convex and normalized by $\int e^{-u}=1$.
--
--   Then there exist $c,C\in\mathbb R$ with $C\ge0$ and $u(x)-c\ge1$ for every $x$ such that, writing
--   $$
--   \chi_R(x)=\operatorname{smoothTransition}\left(2-\frac{u(x)-c}{R}\right),
--   $$
--   and
--   $$
--   L\chi_R=\operatorname{tr}\bigl((\nabla^2u)^{-1}\nabla^2\chi_R\bigr)-\nabla V(\nabla u)\cdot\nabla\chi_R,
--   $$
--   for every $R\ge1$, $\chi_R$ is $C^1$, compactly supported, has a Lipschitz gradient, and satisfies $0\le\chi_R\le1$. For each $x$, $R\mapsto\chi_R(x)$ is monotone on $[1,\infty)$ and tends to $1$. Moreover, $L\chi_R$ is integrable with respect to the tilted measure $e^{-u}dx$, and
--
--   $$
--   \int |L\chi_R|\,d(e^{-u}dx)\le\frac{C}{R}.
--   $$
--
--   The same integral tends to $0$ as $R\to\infty$. This is an existence statement for a cutoff family, not an estimate for arbitrary cutoffs.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/WeakCutoff.lean#L772-L838 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.WeakCutoff`, declaration `FunctionalInequalities.Analysis.exists_scaled_weak_inverse_hessian_cutoffs`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.exists_scaled_weak_inverse_hessian_cutoffs_408915f {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G LF : NNReal}
    (hu : ContDiff ℝ 1 u) (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u x).PosDef)
    (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1) :
    ∃ c C : ℝ, 0 ≤ C ∧ (∀ x, 1 ≤ u x - c) ∧
      let χ := fun R x => Real.smoothTransition (2 - (u x - c) / R)
      let Lχ := fun R x => ((hessianMatrix u x)⁻¹ * hessianMatrix (χ R) x).trace -
        fderiv ℝ V (gradient u x) (gradient (χ R) x)
      (∀ R : ℝ, 1 ≤ R → ContDiff ℝ 1 (χ R) ∧ HasCompactSupport (χ R) ∧
        (∃ K : NNReal, LipschitzWith K (gradient (χ R))) ∧
        ∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
      (∀ x, MonotoneOn (fun R => χ R x) (Ici 1)) ∧
      (∀ x, Tendsto (fun R => χ R x) atTop (𝓝 1)) ∧
      (∀ R : ℝ, 1 ≤ R → Integrable (Lχ R)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ∧
      (∀ R : ℝ, 1 ≤ R → (∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ C / R) ∧
      Tendsto (fun R : ℝ => ∫ x, |Lχ R x|
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) atTop (𝓝 0) := by sorry
