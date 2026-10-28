-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiffOn_logLaplace_ball_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:55.929988+00:00
-- url     : https://prove2.me/theorems/dd1e2494-e9a9-46a2-a434-95c8dca4c3ef
-- title:
--   Smoothness of the Log-Laplace Transform on a Ball
-- statement:
--   This is the local smoothness statement for the log-Laplace transform, corresponding to the finite-and-smooth assertion in Bizeul–Klartag–Lehec, p. 29.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $\mu$ be a finite nonzero measure on $E$, and let $r>0$. Assume
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   Then the log-Laplace transform
--   $\Lambda_\mu(z)=\log\int e^{\langle z,x\rangle}\,d\mu(x)$ is $C^\infty$ on the open ball $B(0,r)$:
--
--   $$
--   \Lambda_\mu\in C^\infty(B(0,r)).
--   $$
--
--   The nonzero condition is represented by the `NeZero μ` instance, and finiteness by `IsFiniteMeasure μ`. The conclusion is `ContDiffOn ℝ ∞ (logLaplace μ)` on the ball.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiffOn_logLaplace_ball (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ] {r : ℝ}
--       (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
--       ContDiffOn ℝ ∞ (logLaplace μ) (Metric.ball 0 r)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598).
--
--   Previous: [`norm_coordTensor_taylorTensor_inner_sq_le_of_basis`](https://prove2.me/theorems/f6507f16-38d4-4c99-9d45-dccf8890a2d6) · Next: [`cumulant_map_linearIsometryEquiv`](https://prove2.me/theorems/2c6f9c5b-4b75-4b42-9954-60d10b0a3552).
--
--   [Source excerpt, lines 761–763](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L761-L763) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L757-L791 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic

open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [CompleteSpace E]
open scoped ContDiff

theorem FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_readable (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ] {r : ℝ}
    (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiffOn ℝ ∞ (logLaplace μ) (Metric.ball 0 r) := by sorry
