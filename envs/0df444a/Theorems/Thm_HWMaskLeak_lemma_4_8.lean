-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_4_8
-- name    : HWMaskLeak.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:27.527604+00:00
-- url     : https://prove2.me/theorems/aa6c957a-1742-4c80-b1d5-222b401eb60d
-- title:
--   Lemma 4.8 — transference from the full-range model to the $N$-grid
-- statement:
--   Let $Q:=2^n$ with $n\ge3$ and $|N-Q|\le Q/n$, and let $P$ be a real number with $|N-Q|\le P$. Then for every $k\ge2$ and every $s\in G=\mathbb Z/N\mathbb Z$,
--   $$
--   E_k(s)\le E^{\mathrm{bin}}_k(N,s)+\sum_{\ell=1}^{k-1}\binom k\ell\Bigl(\frac PN\Bigr)^{\ell/2}F^{\mathrm{bin}}_{k-\ell}(N)+\Bigl(\frac PN\Bigr)^{k/2}\sqrt n.
--   $$
--   Here $E_k(s)$ sums over the actual weights $W=\mathrm{wt}(G)$, while $E^{\mathrm{bin}}_k$ and $F^{\mathrm{bin}}$ sum over $W_{\mathrm{bin}}=\{0,\dots,n\}$.
--
--   The lemma packages the discrepancy between the residues $\{0,\dots,N-1\}$ and the full $n$-bit range $\{0,\dots,Q-1\}$ into terms controlled by $P/N$ and the model energies.
--
--   Differences from the source:
--   - reading: the standing hypotheses of §4 (p.20: |N − 2ⁿ| ≤ 2ⁿ/n), n otherwise unrestricted → 3 ≤ n together with |N − 2ⁿ| ≤ 2ⁿ/n; reason: §4 is the setting of Theorem 2, which assumes n ≥ 3, and the proof of Lemma 4.10 starts at 3 ≤ n; for n = 1 the slice decomposition of App. D.1 fails (N = 4 has the residue 3 of weight 2 = n + 1)
--   - encoding: (P/N)^{ℓ/2}, (P/N)^{k/2}; 0 ≤ s < N → real powers of P/N ≥ 0; s : ZMod N; reason: same values on every instance
--   - encoding: laws of uniform random shares, total variation distance → normalized counts on finite sets and ½ Σ |P − Q| over W^k (resp. W^m × G); reason: uniform choices on finite sets are counting measures; the summation range contains both supports, so no instance changes
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.8, p.22

import Mathlib
import Definitions.Def_HWMaskLeak_insecurity
import Definitions.Def_HWMaskLeak_insecBin
import Definitions.Def_HWMaskLeak_energyBin

namespace HWMaskLeak

/-- **Lemma 4.8 (Transference)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.8, p.22): let `Q := 2ⁿ` with `n ⩾ 3` and
`|N − Q| ⩽ Q/n` (the standing hypotheses of §4, p.20), and suppose `|N − Q| ⩽ P`. Then for every
`k ⩾ 2` and `0 ⩽ s < N`,
`E_k(s) ⩽ E^bin_k(N, s) + Σ_{ℓ=1}^{k−1} (k choose ℓ) (P/N)^{ℓ/2} F^bin_{k−ℓ}(N) + (P/N)^{k/2} √n`.

**Formalization Note** `E_k(s)` sums over the actual weights `W = wt(G)`; the model quantities over
`W_bin = {0, …, n}`. The powers of `P/N ⩾ 0` are real powers. -/
theorem lemma_4_8 (n N : ℕ) [NeZero N] (hn : 3 ≤ n) (hN : |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n)
    (P : ℝ) (hP : |(N : ℝ) - 2 ^ n| ≤ P) (k : ℕ) (hk : 2 ≤ k) (s : ZMod N) :
    insecurity N k s ≤ insecBin n N k s +
      ∑ ℓ ∈ Finset.Icc 1 (k - 1),
        (k.choose ℓ : ℝ) * (P / N) ^ ((ℓ : ℝ) / 2) * energyBin n N (k - ℓ) +
      (P / N) ^ ((k : ℝ) / 2) * Real.sqrt n := by sorry

end HWMaskLeak
