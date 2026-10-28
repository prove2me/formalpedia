-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_inner_eq_fderiv_logLaplace_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:22.609158+00:00
-- url     : https://prove2.me/theorems/6e9a8c5a-1811-461e-b918-2514d0abe6ef
-- title:
--   Tilted Linear Average as a Log-Laplace Derivative Under All Exponential Moments
-- statement:
--   This is the linear-function identity used in the proof of Proposition 7.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be a finite nonzero measure on a finite-dimensional real inner-product space $E$. Assume that for every $r\in\mathbb R$, $x\mapsto e^{r\|x\|}$ is integrable with respect to $\mu$. Then for all $v,z\in E$,
--
--   $$\operatorname{tiltAverage}_\mu\bigl(x\mapsto\langle v,x\rangle\bigr)(z)
--   =D\Lambda_\mu(z)[v],$$
--
--   where $\Lambda_\mu=\operatorname{logLaplace}(\mu)$.
--
--   The statement identifies the tilted expectation of a linear observable with the corresponding directional derivative of the logarithmic Laplace transform.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tiltAverage_inner_eq_fderiv_logLaplace (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v z : E) :
--       tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Definition modules: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Next: [`tiltAverage_inner_eq_fderiv_logLaplace_of_lt`](https://prove2.me/theorems/e5acfca7-aa88-4d8d-9c36-ad0061799915).
--
--   [Source excerpt, lines 135–137](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L135-L137) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L133-L174 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_readable (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v z : E) :
    tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v := by sorry
