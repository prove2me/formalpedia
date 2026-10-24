-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_408915f
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:10.724153+00:00
-- url     : https://prove2.me/theorems/8319258e-717d-43f7-8eee-e2464f93ea3b
-- title:
--   Weak Derivative of a Trace Quadratic
-- statement:
--   This formalizes the weak differentiation rule for a trace quadratic with locally square-integrable derivative data.
--
--   Let $d,n\in\mathbb N$, let $B\in M_n(\mathbb R)$ be constant, let $A,DA:\mathbb R^d\to M_n(\mathbb R)$, and let $v\in\mathbb R^d$. Assume:
--
--   1. Every entry $A_{ij}$ has weak derivative $(DA)_{ij}$ in direction $v$.
--   2. Every entry of $A$ belongs to $L^\infty$ with respect to volume measure.
--   3. For every compact set $S\subseteq\mathbb R^d$, every entry of $DA$ belongs to $L^2(S)$.
--
--   Then the function $x\mapsto\operatorname{tr}(BA(x)BA(x))$ has weak derivative in direction $v$ given by
--
--   $$
--   2\,\operatorname{tr}(BA(x)B\,DA(x)),
--   $$
--
--   and this derivative belongs to $L^2(S)$ for every compact $S$. The Lean declaration is `hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two`. It is a technical polynomial chain rule; zero dimensions and arbitrary real constant matrices are allowed.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L85-L117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two`; the repository is private at upload time).

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
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_408915f {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
      (fun x => 2 * (B * A x * B * DA x).trace) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => 2 * (B * A x * B * DA x).trace) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by sorry
