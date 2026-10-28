-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_choose_mul_sqrt_envelope_readable
-- name    : FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:58.128809+00:00
-- url     : https://prove2.me/theorems/f0ee94f4-c2c1-45a3-acf2-8e29ffebda5f
-- title:
--   Binomial Envelope Product Identity
-- statement:
--   This formalizes the binomial identity (105) from BKL.
--
--   Let $K\ge0$ and let integers $m,a$ satisfy $1\le a\le m$. For $b_j=\operatorname{envelope}(K,j)=K^{j-1}((j-1)!)^2$, one has
--
--   $$
--   \binom{m-1}{a-1}\sqrt{b_a b_{m-a+1}}
--   =\sqrt{b_m}.
--   $$
--
--   The identity is purely arithmetic and is used to normalize the terms in the cumulant-envelope induction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem choose_mul_sqrt_envelope {K : ℝ} (hK : 0 ≤ K) {m a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) :
--       ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
--         Real.sqrt (envelope K m)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnvelope`](https://prove2.me/theorems/dd70df63-9b7a-4c42-ab12-35ef642d8be7).
--
--   Next: [`sum_choose_mul_sqrt_envelope`](https://prove2.me/theorems/df3413be-ea97-45c4-9aa9-5f4083d525a8).
--
--   [Source excerpt, lines 28–30](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L28-L30) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L26-L86 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, declaration `FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnvelope

theorem FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_readable {K : ℝ} (hK : 0 ≤ K) {m a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) :
    ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
      Real.sqrt (envelope K m) := by sorry
