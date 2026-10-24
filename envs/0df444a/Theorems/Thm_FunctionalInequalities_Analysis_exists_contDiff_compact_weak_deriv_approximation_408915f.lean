-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_compact_weak_deriv_approximation_408915f
-- name    : FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:43.682056+00:00
-- url     : https://prove2.me/theorems/910e787a-503d-4e0a-a821-e54f6e1f6a8b
-- title:
--   Common-Compact-Support Approximation of Two Weak Derivatives
-- statement:
--   This formalizes a supporting density component associated with Lemma 2.4 of Letwin (arXiv:2607.24164v1), with a reviewed relation to the cited result.
--
--   Let $\eta,a,b:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$ and let $v,w$ be vectors. Assume:
--
--   1. $a$ is a weak derivative of $\eta$ along $v$, and $b$ is a weak derivative of $\eta$ along $w$;
--   2. $\eta$, $a$, and $b$ have compact support;
--   3. $a,b\in L^2(\operatorname{vol})$.
--
--   Then there exist a compact set $S$ and smooth compactly supported functions $\theta_m$ such that the supports of $\eta,a,b,\theta_m$, and the directional derivatives $D\theta_m(\cdot)v,D\theta_m(\cdot)w$ lie in $S$, while both derivatives belong to $L^2(\operatorname{vol})$ and
--   $$\|D\theta_m(\cdot)v-a\|_2\to0,\qquad \|D\theta_m(\cdot)w-b\|_2\to0.$$
--
--   The conclusion is a two-direction compact approximation result and does not assert approximation of all coordinate derivatives.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean#L154-L362 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Approximation`, declaration `FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation`; the repository is private at upload time).

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
section CompactWeakDerivativeTesting
noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation_408915f {n : ℕ}
    {η a b : EuclideanSpace ℝ (Fin n) → ℝ} {v w : EuclideanSpace ℝ (Fin n)}
    (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      Function.support (η) ⊆ S ∧ Function.support (a) ⊆ S ∧
      Function.support (b) ⊆ S ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (v)) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (w)) ⊆ S ∧
          MemLp (fun x => fderiv ℝ (θ m) x (v)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          MemLp (fun x => fderiv ℝ (θ m) x (w)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (v) - (a) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (w) - (b) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by sorry
