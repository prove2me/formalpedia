-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_hessian_increment_le_generator_408915f
-- name    : FunctionalInequalities.Analysis.ae_hessian_increment_le_generator_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:43.54602+00:00
-- url     : https://prove2.me/theorems/848863fb-7a65-48bf-8dde-6651b33e5431
-- title:
--   Almost-Everywhere Hessian Increment Coercivity
-- statement:
--   This is a partial formalization of the Hessian coercivity statement associated with Lemma 2.4 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb N$ and let $u,V:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Assume:
--
--   1. $u$ is $C^1$ and $\nabla u$ is Lipschitz.
--   2. $V$ is differentiable and convex on the whole space.
--   3. For almost every $x$, with $H(x)=\operatorname{hessianMatrix}(u,x)$, $H(x)$ is positive definite,
--      $$\log\det H(x)=-u(x)+V(\nabla u(x)),$$
--      and $K I-H(x)$ is positive semidefinite.
--
--   For every increment $h$, for almost every $x$,
--
--   $$\frac{\|H(x+h)-H(x)\|_F^2+\|H(x-h)-H(x)\|_F^2}{2K^2}
--   \le \operatorname{tr}\!\left(H(x)^{-1}H_w(x)\right)
--   -DV(\nabla u(x))(\nabla w(x))+w(x),$$
--
--   where $w(y)=u(y+h)+u(y-h)-2u(y)$ and $H_w=\operatorname{hessianMatrix}(w,\cdot)$. The almost-everywhere qualifier is with respect to Lebesgue measure, and no positivity of $K$ is separately assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1916-L1970 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.ae_hessian_increment_le_generator`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LN11AHessianIncrementCoercivity
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.ae_hessian_increment_le_generator_408915f {n : ℕ} {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : Differentiable ℝ V) (hVc : ConvexOn ℝ univ V) {K : ℝ}
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    (h : EuclideanSpace ℝ (Fin n)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
          ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) / (2 * K ^ 2) ≤
        ((hessianMatrix u x)⁻¹ *
            hessianMatrix (fun y => u (y + h) + u (y - h) - 2 * u y) x).trace -
          fderiv ℝ V (gradient u x) (gradient (fun y => u (y + h) + u (y - h) - 2 * u y) x) +
          (u (x + h) + u (x - h) - 2 * u x) := by sorry
