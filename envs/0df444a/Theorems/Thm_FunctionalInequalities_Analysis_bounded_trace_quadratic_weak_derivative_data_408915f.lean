-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_bounded_trace_quadratic_weak_derivative_data_408915f
-- name    : FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:00.276967+00:00
-- url     : https://prove2.me/theorems/aaaaffc7-b392-4f62-8421-ba7dcdeef06b
-- title:
--   Bounded Trace Quadratic Derivative Data
-- statement:
--   This packages boundedness, local integrability, and weak derivative data for a trace quadratic.
--
--   Let $d,n\in\mathbb N$, let $B\in M_n(\mathbb R)$, let $A:\mathbb R^d\to M_n(\mathbb R)$, let $DA:\mathbb R^d\to M_n(\mathbb R)$ be indexed by coordinate directions, and let $M\in[0,\infty)$ be represented by an `NNReal`. Assume:
--
--   1. Every entry of $A$ is measurable.
--   2. For all $x,i,j$, $\|A_{ij}(x)\|\le M$.
--   3. Each entry of $A$ has the stated weak derivative $DA_k$ in the coordinate direction given by `EuclideanSpace.basisFun`.
--   4. Every entry of each $DA_k$ belongs to $L^2$ on every compact restriction of volume measure.
--
--   Then there exists $C\ge0$ such that
--
--   $$
--   \|\operatorname{tr}(BA(x)BA(x))\|\le C
--   $$
--
--   for every $x$, the trace quadratic is locally integrable, and for every coordinate $k$ its weak derivative is
--
--   $$
--   2\,\operatorname{tr}(BA(x)B\,DA_k(x)),
--   $$
--
--   with this derivative in $L^2$ on every compact set. The declaration is `bounded_trace_quadratic_weak_derivative_data`; all finite ambient and matrix dimensions, including zero dimensions, are permitted.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L209-L263 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
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
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
section BoundedTraceQuadratic
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data_408915f {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (DA : Fin d → EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    {M : NNReal}
    (hmeas : ∀ i j, Measurable (fun x => A x i j))
    (hbound : ∀ x i j, ‖A x i j‖ ≤ (M : ℝ))
    (hweak : ∀ k i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA k x i j)
      (EuclideanSpace.basisFun (Fin d) ℝ k))
    (hDA2 : ∀ k i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA k x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖(B * A x * B * A x).trace‖ ≤ C) ∧
      LocallyIntegrable (fun x => (B * A x * B * A x).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) ∧
      ∀ k : Fin d,
        HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
          (fun x => 2 * (B * A x * B * DA k x).trace)
          (EuclideanSpace.basisFun (Fin d) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
          MemLp (fun x => 2 * (B * A x * B * DA k x).trace) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by sorry
