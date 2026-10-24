-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_weightedLaplacian_gamma_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:27.821795+00:00
-- url     : https://prove2.me/theorems/10ab3b43-2d9a-48ba-8655-44ecfa12fd2b
-- title:
--   Integrability of the Weighted Laplacian of Γ
-- statement:
--   This is a compact-support integrability lemma for the weighted Laplacian applied to a carré-du-champ function.
--
--   Let $m$ be a measure on a finite-dimensional real inner-product space, let $U$ be $C^2$, and let $f$ be $C^3$ with compact support. Then
--
--   $$\mathcal L\bigl(\Gamma(f,f)\bigr)\in L^1\bigl(m.\operatorname{tilted}(-U)\bigr).$$
--
--   Here `weightedLaplacian` is $\mathcal L$ and `gamma f f` is $\Gamma(f,f)=\|\nabla f\|^2$. The statement provides the integrability needed in compactly supported Bochner calculations.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L112-L131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma`; the repository is private at upload time).

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
omit [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma_408915f {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => weightedLaplacian U (fun y => gamma f f y) x)
      (m.tilted (-U)) := by sorry
