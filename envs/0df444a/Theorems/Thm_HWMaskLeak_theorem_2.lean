-- Prove2me | Theorems.Thm_HWMaskLeak_theorem_2
-- name    : HWMaskLeak.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:36:48.97876+00:00
-- url     : https://prove2.me/theorems/f9d7bbeb-a501-4ed0-a06a-fcf0e773b314
-- title:
--   Theorem 2 with Corollary 4 — $E_k(s)\le\Delta_{k-1}\le(cn)^{-k/2+5/4}$ for $|N-2^n|\le2^n/n$
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $n\ge3$, let $N$ satisfy $|N-2^n|\le2^n/n$, and fix an integer $k\ge3$. Then for every secret $s\in\{0,1,\dots,N-1\}$,
--
--   1. $E_k(s)\le\Delta_{k-1}$,
--   2. $\Delta_{k-1}\le(cn)^{-k/2+5/4}$, and
--   3. $E_k(s)\le(cn)^{-k/2+5/4}$.
--
--   Here $E_k(s)$ is the total variation distance between the Hamming weights of a uniform $k$-party additive sharing of $s$ modulo $N$ and those of a sharing of a uniform secret (eq. (1)), and $\Delta_{k-1}$ is the distance (3) in which the sum of the first $k-1$ shares is revealed in full.
--
--   Part 3 is Theorem 2: Hamming-weight leakage from three or more additive shares vanishes polynomially in $n$ for every modulus in the near-dyadic window, without primality assumptions. Parts 1–2 are the "Security threshold" box of p.6: the bound survives when the last share is public.
--
--   **Formalization Note** $G=\mathbb Z/N\mathbb Z$ is `ZMod N`; the constant $c$ is chosen before $n$, $N$, $k$ and $s$; the exponent is a real power.
--
--   Differences from the source:
--   - generalization: Theorem 2: E_k(s) ≤ (cn)^{−k/2+5/4} → also E_k(s) ≤ Δ_{k−1} and Δ_{k−1} ≤ (cn)^{−k/2+5/4} with the same absolute c; reason: the box on p.6 states E_k ≤ Δ_{k−1} ≤ C_k n^{−k/2+5/4} (Lemma 3.1 and Corollary 4); with the paper's convention C_k = C^k (p.16) the constant converts to (cn) form with c = C^{−12} exactly as in the proof of Theorem 2 (p.23); the third clause is Theorem 2 verbatim, so the statement specializes to it
--   - encoding: s ∈ {0, 1, …, N − 1} → s : ZMod N with [NeZero N]; reason: the window with n ≥ 3 forces N ≥ 16/3, so NeZero N excludes no instance
--   - encoding: laws of uniform random shares, total variation distance → normalized counts on finite sets and ½ Σ |P − Q| over W^k (resp. W^m × G); reason: uniform choices on finite sets are counting measures; the summation range contains both supports, so no instance changes
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Theorem 2, p.20; the boxed Security threshold, p.6; Corollary 4, p.53; Lemma 3.1, p.18

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity
import Definitions.Def_HWMaskLeak_maskSumDist

namespace HWMaskLeak

/-- **Theorem 2 (near-dyadic moduli upper bound), with Corollary 4 and Lemma 3.1** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…),
Theorem 2, p.20; the boxed "Security threshold", p.6; Corollary 4, p.53; Lemma 3.1, p.18): there is an
absolute constant `c > 0` such that for every `n ⩾ 3`, every `N` with `|N − 2ⁿ| ⩽ 2ⁿ/n`, every
integer `k ⩾ 3` and every secret `s ∈ ℤ/Nℤ`,
`E_k(s) ⩽ Δ_{k−1} ⩽ (cn)^{−k/2+5/4}`, and in particular `E_k(s) ⩽ (cn)^{−k/2+5/4}`.

**Formalization Note** `E_k(s)` is `insecurity N k s` (eq. (1)) and `Δ_{k−1}` is
`maskSumDist N (k − 1)` (eq. (3)); `G = ZMod N` with `[NeZero N]`, which the window implies. The
constant `c` is chosen before `n, N, k, s`. The `Δ` clause with an absolute `c` reads Corollary 4's
`≪_k` with the paper's convention `C_k = C^k` (p.16), converted as in the proof of Theorem 2 (p.23).
The exponent is a real power. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ (n N k : ℕ) [NeZero N], 3 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n → 3 ≤ k →
      ∀ s : ZMod N,
        insecurity N k s ≤ maskSumDist N (k - 1) ∧
        maskSumDist N (k - 1) ≤ (c * n) ^ (-(k : ℝ) / 2 + 5 / 4) ∧
        insecurity N k s ≤ (c * n) ^ (-(k : ℝ) / 2 + 5 / 4) := by sorry

end HWMaskLeak
