-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Line_laplaceMeasure_mgf_408915f
-- name    : FunctionalInequalities.Probability.Line.laplaceMeasure_mgf_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:37:30.701835+00:00
-- url     : https://prove2.me/theorems/49767996-54b7-49d4-a253-b53b85e21a2f
-- title:
--   Moment Generating Function of the Laplace Measure
-- statement:
--   This lemma states the moment generating function of the Laplace measure within the indicated parameter range.
--
--   Let $\beta,w\in\mathbb R$ satisfy $\beta>0$ and $|w|<\beta$. Let $\eta_\beta=$ `laplaceMeasure` $\beta$, the measure on $\mathbb R$ with Lebesgue density $(\beta/2)e^{-\beta|s|}$. Then
--   $$
--   s\mapsto e^{ws}\in L^1(\eta_\beta),\qquad
--   M_{\eta_\beta}(w)=\frac{\beta^2}{\beta^2-w^2},
--   $$
--   where $M_{\eta_\beta}(w)=\int e^{ws}\,d\eta_\beta(s)$ is `ProbabilityTheory.mgf` applied to the identity random variable.
--
--   This gives a law-level exponential-integrability and transform formula, restricted to $|w|<\beta$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Line/Laplace.lean#L236-L256 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Line.Laplace`, declaration `FunctionalInequalities.Probability.Line.laplaceMeasure_mgf`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.MGFAnalytic

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Line
end FunctionalInequalities.Probability.Line
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Line
section Moments
open ProbabilityTheory Filter Set
open scoped Topology

theorem FunctionalInequalities.Probability.Line.laplaceMeasure_mgf_408915f {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    Integrable (fun s : ℝ => Real.exp (w * s)) (laplaceMeasure β) ∧
      mgf id (laplaceMeasure β) w = β ^ 2 / (β ^ 2 - w ^ 2) := by sorry
