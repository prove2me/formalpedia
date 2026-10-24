-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_compact_mul_data_408915f
-- name    : FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:56.057821+00:00
-- url     : https://prove2.me/theorems/940d73c0-20b4-4dd5-b2aa-3eaf32f43e40
-- title:
--   Localized Weak Product Data
-- statement:
--   This is a localized product rule that also supplies support and integrability information. It is listed as a partial formalization of Theorem 2.5 of Letwin2026.
--
--   Let $n\in\mathbb{N}$, let $f,df:\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)\to\mathbb{R}$, and let $v$ be a vector in the same space. Assume:
--
--   1. `HasWeakDerivAlong f df v`.
--   2. For every compact $S$, $df\in L^2(\operatorname{volume}|_S)$.
--   3. For every compact $S$, $f\in L^\infty(\operatorname{volume}|_S)$, expressed as `MemLp` with exponent $\top$.
--   4. $\psi$ is $C^1$ and compactly supported.
--
--   Then `HasWeakDerivAlong` holds for $\psi f$ with derivative
--
--   $$x\mapsto \psi(x)df(x)+D\psi(x)[v]f(x).$$
--
--   Moreover, both this product and its displayed weak derivative have compact support, and the derivative belongs globally to $L^2(\operatorname{volume})$. This packages the regularity properties needed for compactly supported testing.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1353-L1382 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data`; the repository is private at upload time).

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
section SharedCompactLocalTools
open MeasureTheory Set Filter
open scoped ContDiff RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data_408915f {n : ℕ}
    {f df : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (h : HasWeakDerivAlong f df v)
    (hdf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    HasWeakDerivAlong (fun x => ψ x * f x)
      (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) v ∧
    HasCompactSupport (fun x => ψ x * f x) ∧
    HasCompactSupport (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) ∧
    MemLp (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
