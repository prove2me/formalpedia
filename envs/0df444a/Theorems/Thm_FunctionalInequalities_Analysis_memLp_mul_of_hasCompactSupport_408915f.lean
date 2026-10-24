-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_memLp_mul_of_hasCompactSupport_408915f
-- name    : FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:45.91792+00:00
-- url     : https://prove2.me/theorems/5db32d74-a9d1-4422-a071-ee7cb3d93574
-- title:
--   Compactly Supported Cutoff Preserves Global $L^2$ Integrability
-- statement:
--   This statement shows that a compactly supported cutoff converts local $L^2$ control into global $L^2$ control.
--
--   Let $n\in\mathbb{N}$ and let $f,\chi:\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)\to\mathbb{R}$. Assume that $\chi$ is continuous and compactly supported. Assume also that, for every compact set $S$, the restriction of $f$ to $S$ belongs to $L^2$ with respect to restricted Lebesgue measure:
--
--   $$f\in L^2(\operatorname{volume}|_S).$$
--
--   Then
--
--   $$\chi f\in L^2(\operatorname{volume}).$$
--
--   The exponent is the Lean `MemLp` exponent $2$, and the conclusion uses the full volume measure. This is a reusable localization lemma.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L185-L207 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport`; the repository is private at upload time).

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
section WeakProducts
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

theorem FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_408915f {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
