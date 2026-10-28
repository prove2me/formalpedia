-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_choose_mul_sqrt_envelope_readable
-- name    : FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:57.852986+00:00
-- url     : https://prove2.me/theorems/df3413be-ea97-45c4-9aa9-5f4083d525a8
-- title:
--   Summed Binomial Envelope Identity
-- statement:
--   This formalizes the summation identity (106) from BKL.
--
--   Let $K\ge0$ and let $m\ge3$. With $b_j=\operatorname{envelope}(K,j)$,
--
--   $$
--   \sum_{a=2}^{m-2}
--   \binom{m-1}{a-1}\sqrt{b_a b_{m-a+1}}
--   =(m-3)\sqrt{b_m}.
--   $$
--
--   The identity counts the $m-3$ terms in the indicated integer interval and is used in the scalar envelope recurrence.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_choose_mul_sqrt_envelope {K : ℝ} (hK : 0 ≤ K) {m : ℕ} (hm : 3 ≤ m) :
--       ∑ a ∈ Finset.Icc 2 (m - 2),
--           ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
--         ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K m)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7).
--
--   Supporting theorems: [`choose_mul_sqrt_envelope`](https://prove2.me/theorems/f0ee94f4-c2c1-45a3-acf2-8e29ffebda5f).
--
--   Previous: [`choose_mul_sqrt_envelope`](https://prove2.me/theorems/f0ee94f4-c2c1-45a3-acf2-8e29ffebda5f) · Next: [`absorption_le_envelope`](https://prove2.me/theorems/615a5017-49a3-413a-a89d-db3bf9fa1564).
--
--   [Source excerpt, lines 100–103](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L100-L103) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L98-L127 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, declaration `FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope

theorem FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope_readable {K : ℝ} (hK : 0 ≤ K) {m : ℕ} (hm : 3 ≤ m) :
    ∑ a ∈ Finset.Icc 2 (m - 2),
        ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
      ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K m) := by sorry
