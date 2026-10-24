-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_bounded_weak_matrix_product_entry_408915f
-- name    : FunctionalInequalities.Analysis.bounded_weak_matrix_product_entry_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:11.681951+00:00
-- url     : https://prove2.me/theorems/77f8678c-25b7-4654-a3b5-8b1847371a3b
-- title:
--   Weak Derivatives of a Two-Sided Matrix Product
-- statement:
--   This gives boundedness and weak derivative data for entries of a constant two-sided matrix product.
--
--   Let $d,n\in\mathbb N$, let $S\in M_n(\mathbb R)$ be constant, let $H,DH:\mathbb R^d\to M_n(\mathbb R)$, let $v\in\mathbb R^d$, and let $M\in\mathbb R$. Assume every entry of $H$ has weak derivative given by the corresponding entry of $DH$ in direction $v$, every entry satisfies $\|H_{ab}(x)\|\le M$, and every entry of $DH$ is in $L^2$ on every compact restriction of volume measure.
--
--   For every $i,j\in\operatorname{Fin}(n)$, the entry of $SH(x)S$ satisfies
--
--   $$
--   \|(SH(x)S)_{ij}\|\le\sum_{a,b}\|S_{ia}S_{bj}\|\max(M,0),
--   $$
--
--   has weak derivative $(SDH(x)S)_{ij}$ in direction $v$, and that derivative belongs to $L^2$ on every compact set. The declaration is `bounded_weak_matrix_product_entry` and has no positivity, invertibility, or nonzero-dimension assumptions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L286-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.bounded_weak_matrix_product_entry`; the repository is private at upload time).

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
section BoundedWeakMatrixProduct
open MeasureTheory Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.bounded_weak_matrix_product_entry_408915f {d n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    {H DH : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (M : ℝ)
    (hH : ∀ a b, HasWeakDerivAlong (fun x => H x a b) (fun x => DH x a b) v)
    (hbound : ∀ x a b, ‖H x a b‖ ≤ M)
    (hD : ∀ a b, ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      MemLp (fun x => DH x a b) 2 ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K))
    (i j : Fin n) :
    (∀ x, ‖(S * H x * S) i j‖ ≤
      ∑ q : Fin n × Fin n, ‖S i q.1 * S q.2 j‖ * max M 0) ∧
    HasWeakDerivAlong (fun x => (S * H x * S) i j) (fun x => (S * DH x * S) i j) v ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      MemLp (fun x => (S * DH x * S) i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by sorry
