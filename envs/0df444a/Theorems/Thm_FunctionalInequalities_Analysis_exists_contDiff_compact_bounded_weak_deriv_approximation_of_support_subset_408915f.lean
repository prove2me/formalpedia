-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_408915f
-- name    : FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:57.534478+00:00
-- url     : https://prove2.me/theorems/3fd404bf-4316-49cf-900e-93f0bbdf2531
-- title:
--   Support-Controlled Smooth Weak-Derivative Approximation
-- statement:
--   This formalizes part of the regularity approximation used in Lemma 2.2 of Letwin (arXiv:2607.24164v1), with a reviewed relation to the cited result.
--
--   Let $n\in\mathbb N$, let $\eta:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$ be locally integrable and satisfy $\|\eta(x)\|\le C$ for all $x$, and let $a_i$ be functions indexed by $i\in\operatorname{Fin}(n)$. Let $K$ be compact, assume the supports of $\eta$ and all $a_i$ lie in $K$, and assume:
--
--   1. $\varepsilon>0$;
--   2. each $a_i$ is a weak derivative of $\eta$ along the coordinate basis vector $e_i$;
--   3. each $a_i$ belongs to $L^2(\operatorname{vol})$.
--
--   Then there exist a compact set $S\subseteq\operatorname{cthickening}_\varepsilon(K)$ and smooth compactly supported functions $\theta_m$ such that the supports of $\eta$, all $a_i$, every $\theta_m$, and every coordinate derivative of $\theta_m$ lie in $S$; $\|\theta_m(x)\|\le3C$; each derivative is in $L^2$; and
--   $$\|\partial_{e_i}\theta_m-a_i\|_{L^2(\operatorname{vol})}\longrightarrow0.$$
--   Moreover, $\theta_m(x)\to\eta(x)$ for almost every $x$ with respect to volume.
--
--   This is a support- and radius-controlled density statement, valid in every finite dimension including dimension zero.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L395-L600 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Approximation`, declaration `FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset`; the repository is private at upload time).

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
section BoundedWeakDerivativeApproximation
open MeasureTheory Filter Set Metric
open scoped ContDiff Convolution Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 1200000

theorem FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_408915f {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin n, Function.support (a i) ⊆ K)
    {ε : ℝ} (hε : 0 < ε)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i)
      (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧ S ⊆ cthickening ε K ∧
      Function.support η ⊆ S ∧ (∀ i : Fin n, Function.support (a i) ⊆ S) ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m : ℕ, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧ (∀ x, ‖θ m x‖ ≤ 3 * C) ∧
          ∀ i : Fin n,
            Function.support (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆ S ∧
            MemLp (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) 2
              (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∀ i : Fin n,
          Tendsto (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
            2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by sorry
