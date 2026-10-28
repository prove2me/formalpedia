-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Line_integral_exp_mul_laplaceDensity_readable
-- name    : FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:25.322803+00:00
-- url     : https://prove2.me/theorems/7b9ed9dc-464c-47c0-b655-8b9cc377d49c
-- title:
--   Exponential Integral Against the Laplace Density
-- statement:
--   This lemma evaluates the exponentially weighted Laplace density on its stated local parameter range.
--
--   Let $\beta,w\in\mathbb R$ satisfy $\beta>0$ and $|w|<\beta$. Define $\rho_\beta(s)=(\beta/2)e^{-\beta|s|}$, the function `laplaceDensity` $\beta$. With Lebesgue measure $ds$ on $\mathbb R$,
--   $$
--   s\mapsto e^{ws}\rho_\beta(s)\in L^1(ds),\qquad
--   \int_{\mathbb R}e^{ws}\rho_\beta(s)\,ds=\frac{\beta^2}{\beta^2-w^2}.
--   $$
--
--   The statement supplies the density-level integrability and integral needed for the Laplace moment generating function. It makes no assertion for $|w|\ge\beta$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.Line`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_exp_mul_laplaceDensity {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
--       MeasureTheory.Integrable (fun s => Real.exp (w * s) * laplaceDensity β s) ∧
--         ∫ s, Real.exp (w * s) * laplaceDensity β s = β ^ 2 / (β ^ 2 - w ^ 2)
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069).
--
--   Next: [`laplaceMeasure_mgf`](https://prove2.me/theorems/e6314ac4-2242-4f95-90fa-1ef8e685bab6).
--
--   [Source excerpt, lines 106–108](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Line/Laplace.lean#L106-L108) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Line/Laplace.lean#L104-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Line.Laplace`, declaration `FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Line_Laplace

theorem FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_readable {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    MeasureTheory.Integrable (fun s => Real.exp (w * s) * laplaceDensity β s) ∧
      ∫ s, Real.exp (w * s) * laplaceDensity β s = β ^ 2 / (β ^ 2 - w ^ 2) := by sorry
