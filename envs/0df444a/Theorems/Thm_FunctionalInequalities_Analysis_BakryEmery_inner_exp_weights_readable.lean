-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_exp_weights_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.inner_exp_weights_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:06.912633+00:00
-- url     : https://prove2.me/theorems/4f978fb4-52f2-4f2b-90f6-26d81c887136
-- title:
--   Exponential Integrability of Linear Observables
-- statement:
--   This is a weighted integrability consequence of one exponential norm moment.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $\mu$ be a measure, and assume that for some $r\in\mathbb R$,
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   For every $u\in E$ and every $t<r$,
--
--   $$
--   \int e^{t\|x\|}\,|\langle u,x\rangle|\,d\mu(x)<\infty.
--   $$
--
--   The strict inequality $t<r$ is essential to the stated conclusion. This lemma supplies integrability of linear observables needed for local cumulant and tilt calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_exp_weights {μ : Measure E} {r : ℝ}
--       (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u : E) :
--       ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖⟪u, x⟫‖) μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d).
--
--   Next: [`cumulant_three_eq_integral_of_integrable_exp`](https://prove2.me/theorems/2207a4d5-d176-43bd-8980-82729562a6ee).
--
--   [Source excerpt, lines 82–84](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L82-L84) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean#L82-L97 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local`, declaration `FunctionalInequalities.Analysis.BakryEmery.inner_exp_weights`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.inner_exp_weights_readable {μ : Measure E} {r : ℝ}
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (u : E) :
    ∀ t < r, Integrable (fun x => Real.exp (t * ‖x‖) * ‖⟪u, x⟫‖) μ := by sorry
