-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_flux_eq_neg_forcing_of_bounded_weak_test_408915f
-- name    : FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:42.228881+00:00
-- url     : https://prove2.me/theorems/2d14b470-4793-43d8-8170-87981bbb9e2f
-- title:
--   Bounded Weak-Test Extension of Flux Integration by Parts
-- statement:
--   This is a finite-dimensional weak integration-by-parts extension.
--
--   Let $J_i$ be compact-locally in $L^2$, let $F$ be locally integrable, and suppose every compactly supported $C^1$ test $\psi$ satisfies
--
--   $$
--   \int\sum_iJ_i\,\partial_i\psi\,dx=-\int F\psi\,dx.
--   $$
--
--   Let $\eta$ be locally integrable, bounded by a constant $C$ in norm, and compactly supported. Suppose $a_i$ is a weak derivative of $\eta$ in the $i$-th coordinate direction, each $a_i$ is compactly supported, and each $a_i$ belongs globally to $L^2$. Then all products $J_i a_i$ and $F\eta$ are integrable and
--
--   $$
--   \int\sum_iJ_i(x)a_i(x)\,dx
--   =-\int F(x)\eta(x)\,dx.
--   $$
--
--   This theorem extends a compact $C^1$ test identity to bounded compactly supported weak tests; it includes the case $n=0$.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1268-L1304 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
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
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
section BoundedWeakDerivativeTesting
open MeasureTheory Filter Set
open scoped Topology ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.integral_flux_eq_neg_forcing_of_bounded_weak_test_408915f {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, ∑ i : Fin n, J i x * fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
