-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_contDiff_408915f
-- name    : FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_contDiff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:57.447514+00:00
-- url     : https://prove2.me/theorems/0d8f8871-83bf-448a-9137-2ab8e3f43e19
-- title:
--   Product Rule for Weak Directional Derivatives
-- statement:
--   This is the product rule for a weak directional derivative with a compactly supported $C^1$ multiplier.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with its Borel measurable structure. Let $f,g:E\to\mathbb{R}$ and $v\in E$. Assume `HasWeakDerivAlong f g v`, meaning that $g$ is the weak derivative of $f$ in direction $v$. Let $\chi:E\to\mathbb{R}$ be $C^1$ and compactly supported.
--
--   Then the product $\chi f$ has weak directional derivative
--
--   $$x\mapsto \chi(x)g(x)+D\chi(x)[v]f(x).$$
--
--   Here $D\chi(x)[v]$ is represented by `fderiv ℝ χ x v`. The result is a general weak-calculus lemma for localized test functions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L112-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Basic`, declaration `FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_contDiff`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_contDiff_408915f {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    HasWeakDerivAlong (fun x => χ x * f x) (fun x => χ x * g x + fderiv ℝ χ x v * f x) v := by sorry
