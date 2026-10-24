-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_trace_integral_bound_408915f
-- name    : FunctionalInequalities.Analysis.trace_integral_bound_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:46.686625+00:00
-- url     : https://prove2.me/theorems/045b009d-c965-4eb2-881e-d5872d1c523f
-- title:
--   Trace Integral Bound from Almost-Everywhere Quadratic Expansions
-- statement:
--   This is a technical trace inequality for a convex function with almost-everywhere quadratic expansions.
--
--   Let $u,F,\chi:\mathbb R^n\to\mathbb R$, with $u$ convex and $F$ continuous. Assume that, almost everywhere in $y$, there are a Hermitian positive-definite matrix $B$ and a vector $g$ such that
--
--   1. $F(y)\leq\log\det B$;
--   2. $u$ admits the local quadratic expansion represented by `quadraticAt B y g (u y)` with error at most $\varepsilon\|z-y\|^2$ for every $\varepsilon>0$;
--   3. $\chi$ is $C^2$, compactly supported, and nonnegative.
--
--   Let $H$ be a real matrix satisfying, for every $v\in\mathbb R^n$,
--
--   $$
--   \langle v,Hv\rangle=\int u(y)D^2\chi(y)[v,v] \,dy.
--   $$
--
--   Then every positive-definite matrix $J$ satisfies
--
--   $$
--   \int\bigl(F(y)+\log\det J+n\bigr)\chi(y)\,dy
--   \leq
--   \operatorname{tr}(JH).
--   $$
--
--   The lemma packages the spectral trace comparison needed for the mollified log-determinant estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1254-L1320 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `_private.FunctionalInequalities.Analysis.Convex.Viscosity.0.FunctionalInequalities.Analysis.trace_integral_bound`; the repository is private at upload time).

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
section LT12D8MollifiedLogdetBound
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 800000

lemma FunctionalInequalities.Analysis.trace_integral_bound_408915f {n : ℕ}
    {u F χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hF : Continuous F)
    (hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsHermitian ∧ B.PosDef ∧
        F y ≤ Real.log B.det ∧ ∃ g : EuclideanSpace ℝ (Fin n),
          ∀ ε > 0, ∀ᶠ z in 𝓝 y,
            |u z - quadraticAt B y g (u y) z| ≤ ε * ‖z - y‖ ^ 2)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ y, 0 ≤ χ y)
    (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪v, Matrix.toEuclideanLin H v⟫ =
        ∫ y, u y * iteratedFDeriv ℝ 2 χ y (fun _ => v))
    (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.PosDef) :
    (∫ y, (F y + Real.log J.det + n) * χ y) ≤ (J * H).trace := by sorry
