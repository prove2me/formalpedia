-- Prove2me | Theorems.Thm_HWMaskLeak_Supplement_theorem_4
-- name    : HWMaskLeak.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:02:13.618201+00:00
-- url     : https://prove2.me/theorems/da73e203-a882-4c0f-97a8-0f02ff47590b
-- title:
--   Theorem 4 — Mersenne lower bound: $E_k(0)\ge\frac12\,10^{-k}\,n^{-k/2+1}$ for even $k\ge4$
-- statement:
--   Let $E_k(s)$ be the insecurity of a uniform $k$-party additive sharing of $s\in\mathbb Z/N\mathbb Z$ under Hamming-weight leakage, eq. (1).
--
--   For any integer $n\ge3$ with $N=2^n-1$ and any even integer $k\ge4$,
--   $$
--   E_k(0)\ \ge\ \tfrac12\cdot 10^{-k}\cdot n^{-k/2+1}.
--   $$
--
--   Together with the Mersenne upper bounds this shows that the scale $n^{-1/2}$ per additional share is the correct one for Mersenne moduli, up to the $\log n$ factor and constants exponential in $k$.
--
--   **Formalization Note** The power $n^{-k/2+1}$ is a real power.
--
--   Differences from the source:
--   - encoding: N = 2ⁿ − 1 and the secret 0 ∈ ℤ/Nℤ → N : ℕ with [NeZero N] and hN : N = 2 ^ n - 1, secret (0 : ZMod N); reason: N = 2ⁿ − 1 ≥ 7, so NeZero excludes nothing
--   - encoding: 10^{−k} → ((10 : ℝ) ^ k)⁻¹; reason: same real number
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360358eddae84b7b4ee1bbb418105b7887539046e553046bbedd46125a9), Theorem 4, p.26 (pdf p.26), §5.1

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity

namespace HWMaskLeak.Supplement

open HWMaskLeak

/-- **Theorem 4 (Mersenne lower bound)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Theorem 4, p.26): for any integer `n ⩾ 3` with
`N = 2ⁿ − 1` and any even integer `k ⩾ 4`, `E_k(0) ⩾ ½ · 10^{−k} · n^{−k/2+1}`.

**Formalization Note** `E_k(0)` is the published `insecurity N k 0` (eq. (1)). `10^{−k}` is written
`(10^k)⁻¹`; `n^{−k/2+1}` is a real power. `N = 2ⁿ − 1 ⩾ 7`, so `[NeZero N]` excludes nothing. -/
theorem theorem_4 :
    ∀ (n N k : ℕ) [NeZero N], 3 ≤ n → N = 2 ^ n - 1 → Even k → 4 ≤ k →
      (1 / 2 : ℝ) * ((10 : ℝ) ^ k)⁻¹ * (n : ℝ) ^ (-(k : ℝ) / 2 + 1) ≤ insecurity N k 0 := by sorry

end HWMaskLeak.Supplement
