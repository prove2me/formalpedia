-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_two_eq_centered_moment_of_integrable_exp_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_centered_moment_of_integrable_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:32.683957+00:00
-- url     : https://prove2.me/theorems/1be40a1a-f577-4044-a357-24fac041b6cb
-- title:
--   Second Cumulant as a Centered Second Moment
-- statement:
--   This gives the covariance formula for the second cumulant.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $\mu$ be a probability measure, and let $r>0$ satisfy
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   For every $u,v\in E$,
--
--   $$
--   \kappa_2^\mu(u,v)
--   =
--   \int\langle u,x\rangle\langle v,x\rangle\,d\mu(x)
--   -
--   \left(\int\langle u,x\rangle\,d\mu(x)\right)
--   \left(\int\langle v,x\rangle\,d\mu(x)\right).
--   $$
--
--   Thus the second cumulant is the centered second-moment or covariance pairing. The statement requires no centering assumption, only one positive exponential moment.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulant_two_eq_centered_moment_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
--       {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u v : E) :
--       cumulant μ 2 ![u, v] =
--         (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ) - (∫ x, ⟪u, x⟫ ∂μ) * (∫ x, ⟪v, x⟫ ∂μ)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Supporting theorems: [`contDiffOn_logLaplace_ball`](https://prove2.me/theorems/dd1e2494-e9a9-46a2-a434-95c8dca4c3ef), [`inner_exp_weights`](https://prove2.me/theorems/4f978fb4-52f2-4f2b-90f6-26d81c887136), [`tiltAverage_inner_eq_fderiv_logLaplace_of_lt`](https://prove2.me/theorems/e5acfca7-aa88-4d8d-9c36-ad0061799915).
--
--   Previous: [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis`](https://prove2.me/theorems/d843d70e-8af8-4774-b08a-b195f310d902) · Next: [`iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact`](https://prove2.me/theorems/c850afc5-a923-4019-b001-39ff0f56dd9b).
--
--   [Source excerpt, lines 386–389](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L386-L389) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L384-L441 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_centered_moment_of_integrable_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_centered_moment_of_integrable_exp_readable (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u v : E) :
    cumulant μ 2 ![u, v] =
      (∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ) - (∫ x, ⟪u, x⟫ ∂μ) * (∫ x, ⟪v, x⟫ ∂μ) := by sorry
