-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_RegularPotential_integrable_exp_mul_norm_readable
-- name    : FunctionalInequalities.KLS.RegularPotential.integrable_exp_mul_norm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:12.835134+00:00
-- url     : https://prove2.me/theorems/648161d3-ee7c-4a57-800c-c9037b227a1d
-- title:
--   Exponential Norm Moments of a Regular Potential Law
-- statement:
--   This auxiliary integrability result concerns the regular laws of Section 2, (12), p. 5 (unnumbered), of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a complete finite-dimensional real inner product space with its Borel measurable structure. Let $V:E\to\mathbb R$ and $a,b\in\mathbb R$ satisfy `RegularPotential` $V\ a\ b$: $a,b>0$, $V$ is smooth with every derivative of polynomial growth, and $a\operatorname{Id}\le D^2V\le b\operatorname{Id}$. Let $\mu=\operatorname{vol}.\operatorname{tilted}(-V)$ (`Measure.tilted`), the normalized law with density proportional to $e^{-V}$.
--
--   For every real $r$,
--   $$
--   x\mapsto e^{r\|x\|}\in L^1(\mu).
--   $$
--
--   The statement provides exponential-moment integrability for subsequent analytic results. It requires neither centering nor isotropy.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.RegularPotential`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_exp_mul_norm (hV : RegularPotential V a b) (r : ℝ) :
--       Integrable (fun x => Real.exp (r * ‖x‖)) ((volume : Measure E).tilted (-V))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342).
--
--   [Source excerpt, lines 165–166](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Basic.lean#L165-L166) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Section 2, (12), p. 5 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Basic.lean#L164-L197 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Regular.Basic`, declaration `FunctionalInequalities.KLS.RegularPotential.integrable_exp_mul_norm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic

open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {V : E → ℝ} {a b : ℝ}

theorem FunctionalInequalities.KLS.RegularPotential.integrable_exp_mul_norm_readable (hV : RegularPotential V a b) (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖)) ((volume : Measure E).tilted (-V)) := by sorry
