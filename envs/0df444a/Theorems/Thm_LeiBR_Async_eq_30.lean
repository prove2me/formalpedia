-- Prove2me | Theorems.Thm_LeiBR_Async_eq_30
-- name    : LeiBR.Async.eq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:26.706828+00:00
-- url     : https://prove2.me/theorems/63f31d37-948b-4fa6-a0f3-7452d42ef681
-- title:
--   (30) — $\sum_{k=1}^K \beta^k \le \int_1^{K+1}\beta^x\,dx \le \beta^{K+1}/\ln\beta$ for $\beta>1$
-- statement:
--   Let $\beta > 1$ and $K \ge 0$ an integer. Then
--   $$\sum_{k=1}^{K}\beta^k \le \int_1^{K+1}\beta^x\,dx \le \frac{\beta^{K+1}}{\ln\beta}.$$
--
--   The inequality bounds the total number of stochastic gradient steps, a geometric sum of the per-iteration step counts, in the proof of Theorem 3.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 12, §3.4, (30)

import Mathlib

namespace LeiBR.Async

/-- Inequality (30) (§3.4, p. 12): for `β > 1` and every `K`,
`Σ_{k=1}^{K} β^k ≤ ∫_1^{K+1} β^x dx ≤ β^{K+1}/ln β`. -/
theorem eq_30 (β : ℝ) (hβ : 1 < β) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, β ^ k) ≤ ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x ∧
      (∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x) ≤ β ^ ((K : ℝ) + 1) / Real.log β := by sorry

end LeiBR.Async
