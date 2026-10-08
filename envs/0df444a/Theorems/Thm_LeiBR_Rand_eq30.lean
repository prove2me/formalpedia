-- Prove2me | Theorems.Thm_LeiBR_Rand_eq30
-- name    : LeiBR.Rand.eq30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:33.671978+00:00
-- url     : https://prove2.me/theorems/cc4513f3-0ea8-4004-8db2-ea0b3d548922
-- title:
--   (30) — $\sum_{k=1}^K \beta^k \le \int_1^{K+1}\beta^x\,dx \le \beta^{K+1}/\ln\beta$ for $\beta > 1$
-- statement:
--   For every real $\beta > 1$ and every integer $K \ge 0$,
--   $$\sum_{k=1}^{K}\beta^k \le \int_1^{K+1}\beta^x\,dx \le \frac{\beta^{K+1}}{\ln\beta}.$$
--
--   It converts the geometric growth of the per-iteration work into the closed-form complexity bounds (27) and (34).
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 12, §3.4, (30)

import Mathlib

namespace LeiBR.Rand

/-- (30), §3.4, p. 12: for `β > 1` and every `K`,
`∑_{k=1}^K β^k ≤ ∫_1^{K+1} β^x dx ≤ β^{K+1}/ln β`. -/
theorem eq30 (β : ℝ) (hβ : 1 < β) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, β ^ k ≤ ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x ∧
    ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x ≤ β ^ ((K : ℝ) + 1) / Real.log β := by sorry

end LeiBR.Rand
