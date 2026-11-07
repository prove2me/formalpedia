-- Prove2me | Theorems.Thm_HWMaskLeak_corollary_4
-- name    : HWMaskLeak.corollary_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:30.132431+00:00
-- url     : https://prove2.me/theorems/43f7eea5-67bc-4bd3-8491-572fc7df0abc
-- title:
--   Corollary 4 — transference for $\Delta_m$ and $\Delta_m\ll_m n^{-(m-1)/2+1/4}$
-- statement:
--   Let $Q:=2^n$ with $n\ge3$ and $|N-Q|\le Q/n$ (the standing hypotheses of §4).
--
--   1. If $|N-Q|\le P$, then for every $m\ge2$,
--   $$
--   \Delta_m\le\Delta^{\mathrm{bin}}_m(N)+\Bigl(\frac PN\Bigr)^{m/2}\sqrt n+\sum_{0<\ell<m}\binom m\ell\Bigl(\frac PN\Bigr)^{\ell/2}F^{\mathrm{bin}}_{m-\ell}(N).
--   $$
--   2. There is an absolute constant $C\ge1$ such that for every $m\ge2$, every $n\ge3$ and every $N$ with $|N-2^n|\le2^n/n$,
--   $$
--   \Delta_m\le C^m\,n^{-(m-1)/2+1/4}.
--   $$
--   With $m=k-1$ the second part reads $\Delta_{k-1}\le C^{k-1}n^{-k/2+5/4}$ for every $k\ge3$.
--
--   This extends the upper bound from the insecurity $E_k$ to the stronger quantity $\Delta_{k-1}$, in which the sum of the first $k-1$ shares is revealed in full; it is what the preprocessed LWPR application (Theorem 7) uses.
--
--   Differences from the source:
--   - reading: the standing hypotheses of §4 (p.20: |N − 2ⁿ| ≤ 2ⁿ/n), n otherwise unrestricted → 3 ≤ n together with |N − 2ⁿ| ≤ 2ⁿ/n; reason: §4 is the setting of Theorem 2, which assumes n ≥ 3, and the proof of Lemma 4.10 starts at 3 ≤ n; for n = 1 the slice decomposition of App. D.1 fails (N = 4 has the residue 3 of weight 2 = n + 1)
--   - reading: Δ_m ≪_m n^{−(m−1)/2+1/4} → ∃ C ≥ 1 absolute, ∀ m ≥ 2, ∀ n ≥ 3, ∀ N in the window: Δ_m ≤ C^m n^{−(m−1)/2+1/4}; reason: §2.1, p.16 fixes the convention that the constant of ≪_k is C^k for an absolute C independent of n, N and the secret; this is the stronger reading of ≪_m
--   - encoding: (P/N)^{m/2}, n^{−(m−1)/2+1/4} → real powers (Real.rpow) of nonnegative reals; reason: P ≥ |N − Q| ≥ 0, so P/N ≥ 0 and the powers are the usual ones
--   - encoding: laws of uniform random shares, total variation distance → normalized counts on finite sets and ½ Σ |P − Q| over W^k (resp. W^m × G); reason: uniform choices on finite sets are counting measures; the summation range contains both supports, so no instance changes
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. D.2, Corollary 4, p.53

import Mathlib
import Definitions.Def_HWMaskLeak_maskSumDist
import Definitions.Def_HWMaskLeak_maskSumDistBin
import Definitions.Def_HWMaskLeak_energyBin

namespace HWMaskLeak

/-- **Corollary 4** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. D.2, Corollary 4, p.53): let `Q := 2ⁿ` with `n ⩾ 3` and
`|N − Q| ⩽ Q/n` (the standing hypotheses of §4, p.20).
1. If `|N − Q| ⩽ P`, then for every `m ⩾ 2`,
   `Δ_m ⩽ Δ^bin_m(N) + (P/N)^{m/2} √n + Σ_{0<ℓ<m} (m choose ℓ) (P/N)^{ℓ/2} F^bin_{m−ℓ}(N)`.
2. `Δ_m ≪_m n^{−(m−1)/2+1/4}`: there is an absolute `C ⩾ 1` with
   `Δ_m ⩽ C^m n^{−(m−1)/2+1/4}` for every `m ⩾ 2`, `n ⩾ 3` and `N` in the window.

**Formalization Note** `≪_m` is read with the paper's convention `C_m = C^m`, `C` absolute (§2.1,
p.16). The powers `(P/N)^{ℓ/2}` and the exponent of `n` are real powers; `P/N ⩾ 0`. -/
theorem corollary_4 :
    (∀ (n N : ℕ) [NeZero N], 3 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n →
      ∀ P : ℝ, |(N : ℝ) - 2 ^ n| ≤ P → ∀ m : ℕ, 2 ≤ m →
        maskSumDist N m ≤ maskSumDistBin n N m + (P / N) ^ ((m : ℝ) / 2) * Real.sqrt n +
          ∑ ℓ ∈ Finset.Ioo 0 m,
            (m.choose ℓ : ℝ) * (P / N) ^ ((ℓ : ℝ) / 2) * energyBin n N (m - ℓ)) ∧
    (∃ C : ℝ, 1 ≤ C ∧ ∀ (m n N : ℕ) [NeZero N], 2 ≤ m → 3 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n →
      maskSumDist N m ≤ C ^ m * (n : ℝ) ^ (-((m : ℝ) - 1) / 2 + 1 / 4)) := by sorry

end HWMaskLeak
