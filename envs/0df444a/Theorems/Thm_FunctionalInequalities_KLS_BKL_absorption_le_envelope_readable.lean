-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_absorption_le_envelope_readable
-- name    : FunctionalInequalities.KLS.BKL.absorption_le_envelope_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:49.923986+00:00
-- url     : https://prove2.me/theorems/615a5017-49a3-413a-a89d-db3bf9fa1564
-- title:
--   Scalar Absorption by the Cumulant Envelope
-- statement:
--   This formalizes the scalar absorption estimate after BKL (106), p. 27.
--
--   Let $C,K\in\mathbb{R}$ satisfy $C\ge0$, $K\ge9C$, and $K\ge64$. For an integer $m\ge3$, let
--
--   $$
--   b_j=\operatorname{envelope}(K,j)=K^{j-1}((j-1)!)^2.
--   $$
--
--   Then
--
--   $$
--   2Cm^2b_{m-1}+4(m-3)\sqrt{b_{m-1}b_m}\le b_m.
--   $$
--
--   This is an arithmetic estimate only; it does not assert a cumulant bound or complete the induction by itself.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem absorption_le_envelope {K C : ℝ} (hC : 0 ≤ C) (hK9 : 9 * C ≤ K) (hK64 : 64 ≤ K)
--       {m : ℕ} (hm : 3 ≤ m) :
--       2 * C * (m : ℝ) ^ 2 * envelope K (m - 1) +
--           4 * ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K (m - 1) * envelope K m) ≤
--         envelope K m
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7).
--
--   Previous: [`sum_choose_mul_sqrt_envelope`](https://prove2.me/theorems/df3413be-ea97-45c4-9aa9-5f4083d525a8).
--
--   [Source excerpt, lines 133–137](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L133-L137) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L129-L242 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, declaration `FunctionalInequalities.KLS.BKL.absorption_le_envelope`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope

theorem FunctionalInequalities.KLS.BKL.absorption_le_envelope_readable {K C : ℝ} (hC : 0 ≤ C) (hK9 : 9 * C ≤ K) (hK64 : 64 ≤ K)
    {m : ℕ} (hm : 3 ≤ m) :
    2 * C * (m : ℝ) ^ 2 * envelope K (m - 1) +
        4 * ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K (m - 1) * envelope K m) ≤
      envelope K m := by sorry
