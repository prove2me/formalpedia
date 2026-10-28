-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_cond_readable
-- name    : FunctionalInequalities.KLS.LogConcave.cond_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:44.526046+00:00
-- url     : https://prove2.me/theorems/a9c544d7-ce6e-4338-89f4-f44a4207b027
-- title:
--   Log-Concavity Under Convex Conditioning
-- statement:
--   This formalizes the conditioning statement used in the compact-support reduction for Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a real normed space with Borel measurable structure, and let $\mu$ be a log-concave probability measure. Let $C\subseteq E$ be convex and closed, and assume $\mu(C)\ne0$. Form the conditional probability measure $\mu[\mid C]$ using `cond_readable`.
--
--   Then the conditional law remains log-concave:
--
--   $$
--   \operatorname{LogConcave}(\mu[\mid C]).
--   $$
--
--   The result applies the compact-set definition of log-concavity and is particularly suited to conditioning on closed balls. It makes no assertion about isotropy or compactness of the conditional law beyond the stated hypotheses.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cond {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--       [MeasurableSpace E] [BorelSpace E] {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
--       {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) (hpos : (μ : Measure E) C ≠ 0) :
--       LogConcave (⟨(μ : Measure E)[|C], cond_isProbabilityMeasure hpos⟩ : ProbabilityMeasure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Transport`](https://prove2.me/theorems/e2b06803-5a96-41cf-bc8d-6b89b02cb255).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Previous: [`map_affineIsometry`](https://prove2.me/theorems/24db795f-31a5-42d9-9329-a7272770b5c9).
--
--   [Source excerpt, lines 216–219](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean#L216-L219) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean#L212-L360 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Transport`, declaration `FunctionalInequalities.KLS.LogConcave.cond`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport

open MeasureTheory Set Topology
open ProbabilityTheory

theorem FunctionalInequalities.KLS.LogConcave.cond_readable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) (hpos : (μ : Measure E) C ≠ 0) :
    LogConcave (⟨(μ : Measure E)[|C], cond_isProbabilityMeasure hpos⟩ : ProbabilityMeasure E) := by sorry
