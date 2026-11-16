-- Prove2me | Theorems.Thm_HWMaskLeak_Supplement_theorem_3
-- name    : HWMaskLeak.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:01:28.108202+00:00
-- url     : https://prove2.me/theorems/1abfef49-ce0d-434f-8cd1-ea221cba34ec
-- title:
--   Theorem 3 — Mersenne moduli, every $n\ge3$: $E_k(s)\le(cn)^{-k/2+1}\log n$
-- statement:
--   Let $E_k(s)$ be the insecurity of a uniform $k$-party additive sharing of $s\in\mathbb Z/N\mathbb Z$ under Hamming-weight leakage, eq. (1).
--
--   There is an absolute constant $c>0$ such that the following holds. Let $n\ge3$ be an integer, $N=2^n-1$, and fix an integer $k\ge3$. Then for every $s\in\{0,1,\dots,N-1\}$,
--   $$
--   E_k(s)\le (cn)^{-k/2+1}\log n .
--   $$
--
--   This refines the near-dyadic upper bound for Mersenne moduli for every exponent $n$, prime or not; the dependence on $k$ is through $c^{-k/2+1}$.
--
--   **Formalization Note** $\log$ is the natural logarithm, multiplying the real power $(cn)^{-k/2+1}$. The constant $c$ is chosen before $n$, $N$, $k$, $s$.
--
--   Differences from the source:
--   - encoding: s ∈ {0, 1, …, N − 1} → s : ZMod N with [NeZero N], N : ℕ and hN : N = 2 ^ n - 1; reason: ZMod N is ℤ/Nℤ, whose canonical representatives are {0, …, N − 1}; N = 2ⁿ − 1 ≥ 7, so NeZero excludes nothing
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360358eddae84b7b4ee1bbb418105b7887539046e553046bbedd46125a9), Theorem 3, p.25 (pdf p.25), §4.4.1

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity

namespace HWMaskLeak.Supplement

open HWMaskLeak

/-- **Theorem 3 (Mersenne-moduli upper bound)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Theorem 3, p.25): there is an absolute
constant `c > 0` such that for every integer `n ⩾ 3`, `N = 2ⁿ − 1`, every integer `k ⩾ 3` and every
`s ∈ {0, 1, …, N − 1}`, `E_k(s) ⩽ (cn)^{−k/2+1} log n`.

**Formalization Note** `E_k(s)` is the published `insecurity N k s` (eq. (1)); `c` is chosen before
`n, N, k, s`. The exponent is a real power and `log` (natural logarithm) multiplies the power, it is
not part of the exponent. `N = 2ⁿ − 1 ⩾ 7`, so `[NeZero N]` excludes nothing. -/
theorem theorem_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n N k : ℕ) [NeZero N], 3 ≤ n → N = 2 ^ n - 1 → 3 ≤ k →
      ∀ s : ZMod N,
        insecurity N k s ≤ (c * n) ^ (-(k : ℝ) / 2 + 1) * Real.log n := by sorry

end HWMaskLeak.Supplement
