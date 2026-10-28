-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_three_eq_integral_of_integrable_exp_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.cumulant_three_eq_integral_of_integrable_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:10.46899+00:00
-- url     : https://prove2.me/theorems/2207a4d5-d176-43bd-8980-82729562a6ee
-- title:
--   Third Cumulant as a Centered Third Moment
-- statement:
--   This formalizes the third-cumulant identity from Bizeul–Klartag–Lehec, Lemma 4.2, p. 18, in its stated local form.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $\mu$ be a probability measure, and let $r>0$ satisfy
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   Assume that $\mu$ is centered, meaning
--   $\int\langle v,x\rangle\,d\mu(x)=0$ for every $v\in E$. Then for all $u,v,w\in E$,
--
--   $$
--   \kappa_3^\mu(u,v,w)
--   =
--   \int \langle u,x\rangle\langle v,x\rangle\langle w,x\rangle\,d\mu(x).
--   $$
--
--   The cumulant is evaluated on the three directions using `cumulant μ 3 ![u, v, w]`. The result assumes only one positive exponential moment, not all exponential moments or log-concavity.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulant_three_eq_integral_of_integrable_exp (μ : Measure E) [IsProbabilityMeasure μ]
--       {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
--       (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
--       cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ
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
--   Previous: [`inner_exp_weights`](https://prove2.me/theorems/4f978fb4-52f2-4f2b-90f6-26d81c887136) · Next: [`memLp_of_polynomial_bound_of_integrable_exp`](https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818).
--
--   [Source excerpt, lines 101–104](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L101-L104) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 4.2, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L99-L170 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.cumulant_three_eq_integral_of_integrable_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_three_eq_integral_of_integrable_exp_readable (μ : Measure E) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hc : ∀ v : E, ∫ x, ⟪v, x⟫ ∂μ = 0) (u v w : E) :
    cumulant μ 3 ![u, v, w] = ∫ x, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂μ := by sorry
