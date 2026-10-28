-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Line_laplaceMeasure_mgf_readable
-- name    : FunctionalInequalities.Probability.Line.laplaceMeasure_mgf_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:27.163053+00:00
-- url     : https://prove2.me/theorems/e6314ac4-2242-4f95-90fa-1ef8e685bab6
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Line`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem laplaceMeasure_mgf {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
--       Integrable (fun s : ℝ => Real.exp (w * s)) (laplaceMeasure β) ∧
--         mgf id (laplaceMeasure β) w = β ^ 2 / (β ^ 2 - w ^ 2)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Supporting theorems: [`integral_exp_mul_laplaceDensity`](https://prove2.me/theorems/7b9ed9dc-464c-47c0-b655-8b9cc377d49c).
--
--   Previous: [`integral_exp_mul_laplaceDensity`](https://prove2.me/theorems/7b9ed9dc-464c-47c0-b655-8b9cc377d49c).
--
--   [Source excerpt, lines 237–239](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Line/Laplace.lean#L237-L239) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Line/Laplace.lean#L236-L256 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Line.Laplace`, declaration `FunctionalInequalities.Probability.Line.laplaceMeasure_mgf`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Line_Laplace

open MeasureTheory
open ProbabilityTheory Filter Set

theorem FunctionalInequalities.Probability.Line.laplaceMeasure_mgf_readable {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    Integrable (fun s : ℝ => Real.exp (w * s)) (laplaceMeasure β) ∧
      mgf id (laplaceMeasure β) w = β ^ 2 / (β ^ 2 - w ^ 2) := by sorry
