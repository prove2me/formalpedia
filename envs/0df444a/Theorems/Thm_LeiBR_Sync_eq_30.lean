-- Prove2me | Theorems.Thm_LeiBR_Sync_eq_30
-- name    : LeiBR.Sync.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:42.44714+00:00
-- url     : https://prove2.me/theorems/27b35f83-2c61-40ca-bd55-f82f3b666d82
-- title:
--   (30) — $\sum_{k=1}^K\beta^k\le\int_1^{K+1}\beta^x\,dx\le\beta^{K+1}/\ln\beta$ for $\beta>1$
-- statement:
--   For every $\beta>1$ and every integer $K\ge0$,
--   $$\sum_{k=1}^K\beta^k\le\int_1^{K+1}\beta^x\,dx\le\frac{\beta^{K+1}}{\ln\beta}.$$
--
--   This bound turns the total number of inner SA steps, a geometric sum, into the closed form of the complexity bound (27).
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, §3.4, proof of Theorem 1, (30), p. 12

import Mathlib

namespace LeiBR.Sync

/-- (30), §3.4, p. 12: for `β > 1` and every `K`,
`∑_{k=1}^{K} β^k ≤ ∫_1^{K+1} β^x dx ≤ β^{K+1}/ln β`. -/
theorem eq_30 (β : ℝ) (hβ : 1 < β) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, β ^ k ≤ ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x ∧
      ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x ≤ β ^ (K + 1) / Real.log β := by sorry

end LeiBR.Sync
