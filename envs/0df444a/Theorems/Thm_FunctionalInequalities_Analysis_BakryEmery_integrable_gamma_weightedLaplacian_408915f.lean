-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_gamma_weightedLaplacian_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_gamma_weightedLaplacian_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:45.27545+00:00
-- url     : https://prove2.me/theorems/dc707dc8-27e1-42df-a862-a3d14634b72e
-- title:
--   Integrability of Γ Against the Weighted Laplacian
-- statement:
--   This is a compact-support integrability lemma for the weighted diffusion operator.
--
--   Let $m$ be a measure on a finite-dimensional real inner-product space, let $U$ be $C^2$, and let $f$ be $C^3$ with compact support. For the tilted measure $m.\operatorname{tilted}(-U)$, the function $x\mapsto\Gamma(f,\mathcal Lf)(x)$ is integrable:
--
--   $$\Gamma(f,\mathcal Lf)\in L^1\bigl(m.\operatorname{tilted}(-U)\bigr).$$
--
--   Here `gamma` denotes $\Gamma(f,g)=\langle\nabla f,\nabla g\rangle$ and `weightedLaplacian` denotes $\mathcal L$. The result supplies an integrability side condition for the compactly supported curvature identities.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L133-L151 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_gamma_weightedLaplacian`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_gamma_weightedLaplacian_408915f {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => gamma f (weightedLaplacian U f) x) (m.tilted (-U)) := by sorry
