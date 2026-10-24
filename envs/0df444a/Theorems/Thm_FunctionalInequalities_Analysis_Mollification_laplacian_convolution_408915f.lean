-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Mollification_laplacian_convolution_408915f
-- name    : FunctionalInequalities.Analysis.Mollification.laplacian_convolution_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:36.671422+00:00
-- url     : https://prove2.me/theorems/3f9ac82d-1143-41ca-96fd-9d285e9a10ef
-- title:
--   Laplacian Commutation with Mollification
-- statement:
--   This states that mollification commutes with the Laplacian for smooth compactly supported scalar functions.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $\varphi$ be a smooth bump centered at $0$. If $g:V\to\mathbb{R}$ is smooth and compactly supported, then for every $x\in V$,
--
--   $$\Delta\bigl((\varphi_{\mathrm{normed}}\ast g)(x)\bigr)
--   =\bigl(\varphi_{\mathrm{normed}}\ast\Delta g\bigr)(x).$$
--
--   Here $\Delta$ is `Laplacian.laplacian`. This provides the second-order analogue of the gradient commutation identity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L387-L435 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `FunctionalInequalities.Analysis.Mollification.laplacian_convolution`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
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
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Derivative
variable (φ : ContDiffBump (0 : V))

theorem FunctionalInequalities.Analysis.Mollification.laplacian_convolution_408915f {g : V → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (x : V) :
    Laplacian.laplacian (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] g) x =
      (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] Laplacian.laplacian g) x := by sorry
