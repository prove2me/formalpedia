-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_gamma_weightedLaplacian_eq_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_gamma_weightedLaplacian_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:29.349016+00:00
-- url     : https://prove2.me/theorems/c3c91ec0-0e17-4c51-85ab-6a38ab879616
-- title:
--   Compactly Supported Gamma-Generator Identity
-- statement:
--   This is the compactly supported integration-by-parts identity for $\Gamma(f,\mathcal Lf)$.
--
--   Let $E$ be finite-dimensional and complete with a real inner product, let $m$ be an additive Haar measure, and let $U,f:E\to\mathbb R$. Assume that $U$ is $C^2$, $f$ is $C^3$, and $f$ has compact support. For $\mu=m.\operatorname{tilted}(-U)$,
--
--   $$\int \Gamma(f,\mathcal L_Uf)\,d\mu=-\int (\mathcal L_Uf)^2\,d\mu.$$
--
--   Here `gamma` is the gradient pairing and `weightedLaplacian` is $\mathcal L_U$. The result is a compact-support component of the curvature and Bochner calculations.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L167-L193 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_gamma_weightedLaplacian_eq`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_gamma_weightedLaplacian_eq_408915f {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    ∫ x, gamma f (weightedLaplacian U f) x ∂(m.tilted (-U)) =
      -∫ x, weightedLaplacian U f x ^ 2 ∂(m.tilted (-U)) := by sorry
