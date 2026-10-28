-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:59.897575+00:00
-- url     : https://prove2.me/theorems/e5acfca7-aa88-4d8d-9c36-ad0061799915
-- title:
--   Tilted Linear Average as a Log-Laplace Derivative Under a Single Exponential Moment
-- statement:
--   This is the local tilt-average/derivative identity for linear observables.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $\mu$ be a finite nonzero measure, and assume that for some $r\in\mathbb R$,
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   If $z\in E$ satisfies $\|z\|<r$, then for every $v\in E$,
--
--   $$
--   \int \langle v,x\rangle\,d\mu_z(x)
--   =
--   D\Lambda_\mu(z)[v],
--   $$
--
--   where $\mu_z$ is the exponential tilt, $\Lambda_\mu=\logLaplace(\mu)$, and the derivative is represented by `fderiv ℝ (logLaplace μ) z v`. Only the single exponential moment at radius $r$ is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tiltAverage_inner_eq_fderiv_logLaplace_of_lt (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
--       {r : ℝ} (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) {z : E} (hz : ‖z‖ < r) (v : E) :
--       tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Previous: [`tiltAverage_inner_eq_fderiv_logLaplace`](https://prove2.me/theorems/6e9a8c5a-1811-461e-b918-2514d0abe6ef) · Next: [`taylorTensor_inner_eq_cumulant`](https://prove2.me/theorems/777bcca0-0906-41de-8616-b3ae233c3880).
--
--   [Source excerpt, lines 178–180](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L178-L180) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L176-L258 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_readable (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    {r : ℝ} (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) {z : E} (hz : ‖z‖ < r) (v : E) :
    tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v := by sorry
