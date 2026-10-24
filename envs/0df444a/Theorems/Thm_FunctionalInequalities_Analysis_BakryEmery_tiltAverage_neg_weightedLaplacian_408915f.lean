-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_neg_weightedLaplacian_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:29.050991+00:00
-- url     : https://prove2.me/theorems/3522da14-12de-4686-819c-23fa2c2a2f4c
-- title:
--   Tilted Generator Identity
-- statement:
--   This formalizes Equation (48) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Equation (48), p. 14.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel measurable structure, and let $m$ be a measure that is an additive Haar measure. Let $V,f:E\to\mathbb R$ satisfy:
--
--   1. $V$ is $C^1$.
--   2. $f$ is $C^2$.
--   3. $f$ has compact support.
--
--   For every $z\in E$, with $\mu=m.\operatorname{tilted}(-V)$, one has
--
--   $$
--   F_{-\mathcal Lf}(z)=\left\langle z,F_{\nabla f}(z)\right\rangle,
--   $$
--
--   where $F_h=\operatorname{tiltAverage}(\mu,h)$ and
--
--   $$
--   \mathcal Lf=\Delta f-\langle\nabla V,\nabla f\rangle.
--   $$
--
--   This is the generator identity used to convert weighted-Laplacian terms into gradient terms in the Taylor-tensor argument.
--
--   **Formalization Note** The statement is total even when $e^{-V}$ is not $m$-integrable: in that case the tilted measure is the zero measure and both sides vanish. No probability-measure assumption is present.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (48), p. 14 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L154-L240 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian_408915f {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (z : E) :
    tiltAverage (m.tilted (-V)) (fun x => -weightedLaplacian V f x) z =
      ⟪z, tiltAverage (m.tilted (-V)) (gradient f) z⟫ := by sorry
