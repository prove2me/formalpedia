-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBoundCompact_two_of_letwinCompact_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:11.158051+00:00
-- url     : https://prove2.me/theorems/5e9f20a0-75af-4b56-97f4-5f51be0ce81a
-- title:
--   Third Cumulant Bound From the Compact Letwin Bound
-- statement:
--   This formalizes the compactly supported part of Bizeul–Klartag–Lehec Lemma 4.2, p. 18.
--
--   Assume `LetwinCompactBound`. Then the compact cumulant bound holds in order $d=2$ with constant $8$:
--
--   $$\operatorname{CumulantBoundCompact}(2,8).$$
--
--   Unfolded, this means that for every dimension $n$, every compactly supported isotropic log-concave probability measure $\mu$ on $\mathbb R^n$, and every vector $u$, the sum of squared third cumulants indexed by pairs of basis directions is at most
--
--   $$8\,\lVert u\rVert^2.$$
--
--   The declaration treats `LetwinCompactBound` as a hypothesis; it does not prove that hypothesis or a general KLS bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cumulantBoundCompact_two_of_letwinCompact (h : LetwinCompactBound) :
--       CumulantBoundCompact 2 8
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Supporting theorems: [`sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis`](https://prove2.me/theorems/d843d70e-8af8-4774-b08a-b195f310d902), [`exists_integrable_exp_norm`](https://prove2.me/theorems/cae54259-25c9-4b6d-b8ab-140080dd2348).
--
--   Next: [`norm_sub_one_le_of_isPositive_mul_self`](https://prove2.me/theorems/eb4c41c1-de2e-4b9b-953d-d2442f523791).
--
--   [Source excerpt, lines 53–54](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L53-L54) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 4.2, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L51-L90 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CompactReduction`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

theorem FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBoundCompact_two_of_letwinCompact_readable (h : LetwinCompactBound) :
    CumulantBoundCompact 2 8 := by sorry
