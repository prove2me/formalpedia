-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_weakDeriv_mul_eq_swap_408915f
-- name    : FunctionalInequalities.Analysis.integral_weakDeriv_mul_eq_swap_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:47.729979+00:00
-- url     : https://prove2.me/theorems/def0829b-3490-4c0f-8de1-b20dbb93da9d
-- title:
--   Weak Derivative Curl Identity
-- statement:
--   This is a compact-support weak integration-by-parts identity for two directional derivatives of the same scalar function.
--
--   Let $f$ have weak derivatives $p$ and $q$ along directions $v$ and $w$, respectively, with $p$ and $q$ locally in $L^2$. Let $\eta$ have weak derivatives $a$ and $b$ along $v$ and $w$, respectively. Assume $\eta,a,b$ have compact support and $a,b$ are globally in $L^2$. Then
--
--   $$
--   \int p(x)b(x)\,dx=\int q(x)a(x)\,dx.
--   $$
--
--   The identity is valid in every finite dimension, including dimension zero, and is a supporting rough-testing statement.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L830-L1076 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.integral_weakDeriv_mul_eq_swap`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.integral_weakDeriv_mul_eq_swap_408915f {n : ℕ}
    {f p q η a b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v w : EuclideanSpace ℝ (Fin n)}
    (hp : HasWeakDerivAlong f p v) (hq : HasWeakDerivAlong f q w)
    (hp2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp p 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hq2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp q 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, q x * a x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
