-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_det_of_locally_memLp_two_408915f
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:47.9262+00:00
-- url     : https://prove2.me/theorems/c71062cd-ba09-499b-874b-80bf6d9183fb
-- title:
--   Weak Derivative of a Determinant Polynomial
-- statement:
--   Let $A(x)$ be a matrix field indexed by a finite type and let $DA(x)$ be a proposed directional derivative field along a direction $v$. Assume every entry $A_{ij}$ has weak derivative $(DA)_{ij}$ along $v$, every entry of $A$ belongs to $L^{\infty}$, and every entry of $DA$ belongs locally to $L^2$ on compact sets. Then $\det A$ has weak derivative
--
--   $$
--   \partial_v\det A(x)=\sum_{\sigma\in S_I}\operatorname{sgn}(\sigma)
--   \sum_i DA_{\sigma(i),i}(x)
--   \prod_{j\ne i}A_{\sigma(j),j}(x),
--   $$
--
--   and this derivative is locally in $L^2$ on every compact set. No symmetry, positivity, invertibility, or classical differentiability is assumed.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L42-L83 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_408915f {d : ℕ} {ι : Type*}
    [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (A x).det)
      (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by sorry
