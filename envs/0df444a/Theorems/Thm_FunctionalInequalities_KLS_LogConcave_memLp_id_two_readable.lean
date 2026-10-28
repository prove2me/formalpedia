-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_memLp_id_two_readable
-- name    : FunctionalInequalities.KLS.LogConcave.memLp_id_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:57.349958+00:00
-- url     : https://prove2.me/theorems/1e1255d8-1cf4-45ef-8f96-0337bafe649e
-- title:
--   Finite Ambient Second Moment
-- statement:
--   This formalizes the finite-second-moment part of the literature statement on moments of log-concave laws, cited in Section 1 of Klartag–Lehec (2022).
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with its measurable Borel structure and second-countable topology, and let $\mu$ be a log-concave probability measure on $E$. No completeness assumption is required in the declaration.
--
--   Then the identity map has finite $L^2$ norm:
--
--   $$
--   \operatorname{MemLp}(\operatorname{id},2,\mu).
--   $$
--
--   Equivalently, the ambient second moment of $\mu$ is finite. The result is useful for defining the barycenter and covariance of a log-concave law; it does not state a Poincaré inequality or any KLS bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem memLp_id_two (hμ : LogConcave μ) : MemLp id 2 (μ : Measure E)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Translation`](https://prove2.me/theorems/90dffb15-6ccb-4069-ada2-b620f287fe68).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`exists_integrable_exp_norm`](https://prove2.me/theorems/cae54259-25c9-4b6d-b8ab-140080dd2348).
--
--   [Source excerpt, lines 53–53](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Translation.lean#L53-L53) · Frozen source `408915f`.
-- source:
--   Source: Klartag–Lehec, Bourgain’s slicing problem and KLS isoperimetry up to polylog (arXiv:2203.15551v2), Section 1 (cited [BGVV, Lemma 2.2.1]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Translation.lean#L50-L71 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Translation`, declaration `FunctionalInequalities.KLS.LogConcave.memLp_id_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Translation

open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  {μ : MeasureTheory.ProbabilityMeasure E}
omit [CompleteSpace E]

theorem FunctionalInequalities.KLS.LogConcave.memLp_id_two_readable (hμ : LogConcave μ) : MemLp id 2 (μ : Measure E) := by sorry
