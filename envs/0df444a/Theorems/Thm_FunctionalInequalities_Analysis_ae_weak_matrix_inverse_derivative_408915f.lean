-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_matrix_inverse_derivative_408915f
-- name    : FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:12:04.17449+00:00
-- url     : https://prove2.me/theorems/dc73fe7d-df84-43c3-820c-eba8e2469966
-- title:
--   Almost-Everywhere Derivative Formula for Weak Matrix Inverses
-- statement:
--   This is a technical almost-everywhere inverse differentiation rule for matrix-valued weak derivatives.
--
--   Let $A,R:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(d))\to\mathbb R^{m\times m}$, with weak directional derivatives $DA,DR$ along a fixed direction. Assume:
--
--   1. Every entry of $A$ and $R$ is locally essentially bounded on compact sets (`MemLp` with exponent $\top$).
--   2. Every entry of $DA$ and $DR$ belongs to local $L^2$ on compact sets.
--   3. Almost everywhere, $R(x)A(x)=I$.
--
--   Then, almost everywhere,
--
--   $$DR(x)=-R(x)\,DA(x)\,R(x).$$
--
--   The dimensions $d$ and $m$ are independent and may be zero. The declaration `ae_weak_matrix_inverse_derivative` assumes the weak derivatives and integrability data as inputs; it does not assume classical differentiability.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L128-L198 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative`; the repository is private at upload time).

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
section WeakMatrixInverse
open MeasureTheory Set Matrix
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative_408915f {d m : ℕ}
    {A R DA DR : EuclideanSpace ℝ (Fin d) → Matrix (Fin m) (Fin m) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hR : ∀ i j, HasWeakDerivAlong (fun x => R x i j) (fun x => DR x i j) v)
    (hA_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => A x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hR_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => R x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDR2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DR x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), R x * A x = 1) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DR x = -(R x * DA x * R x) := by sorry
