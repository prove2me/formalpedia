-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBound_of_compact_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:56.132396+00:00
-- url     : https://prove2.me/theorems/642ea310-0dfa-47d8-b6bd-18048856ed8f
-- title:
--   Extension of Compact Cumulant Bounds
-- statement:
--   This formalizes the compact-support approximation step cited on p. 19 and at the end of Section 6 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), with the literature register associating it with Theorem 4.1.
--
--   Let $d\in\mathbb N$ satisfy $1\le d$, let $b\in\mathbb R$, and assume `CumulantBoundCompact d b`: the cumulant bound holds for compactly supported isotropic log-concave laws. Then the corresponding unrestricted bound holds:
--
--   $$
--   \operatorname{CumulantBound}(d,b).
--   $$
--
--   In particular, the bound applies at every order $d+1\ge2$ to every isotropic log-concave probability law. The declaration transfers a hypothesis about compactly supported laws; it does not produce a numerical value of $b$ or prove the compact bound itself.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulantBound_of_compact {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : CumulantBoundCompact d b) :
--       CumulantBound d b
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Definition modules: [`KLS/BKL/Suspension/Law`](https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3).
--
--   Selected supporting theorems: [`cumulant_map_affine`](https://prove2.me/theorems/ff092742-6b2a-4aa9-b96d-052edb49e94b), [`cumulant_two_eq_centered_moment_of_integrable_exp`](https://prove2.me/theorems/1be40a1a-f577-4044-a357-24fac041b6cb), [`memLp_of_polynomial_bound_of_integrable_exp`](https://prove2.me/theorems/c310b23c-d379-45e3-87b0-6aa7ce729818), [`tendsto_cumulant_cond_closedBall`](https://prove2.me/theorems/5a26c5c6-06d4-47bc-a7e9-de2a1a85735b), [`exists_integrable_exp_norm`](https://prove2.me/theorems/cae54259-25c9-4b6d-b8ab-140080dd2348).
--
--   Previous: [`exists_standardized`](https://prove2.me/theorems/b86ffa3f-dfc6-43a2-8cd2-8a6a6fc5a590).
--
--   [Source excerpt, lines 316–317](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L316-L317) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L313-L396 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CompactReduction`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

theorem FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_of_compact_readable {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (h : CumulantBoundCompact d b) :
    CumulantBound d b := by sorry
