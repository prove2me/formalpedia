-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_4_6
-- name    : HWMaskLeak.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:04.26825+00:00
-- url     : https://prove2.me/theorems/5bcb9431-811f-412c-86b7-c9e4a284bda1
-- title:
--   Lemma 4.6 — model base case $F^{\mathrm{bin}}_1(N)\ll n^{1/4}$
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge3$ and every $N$ with $|N-2^n|\le2^n/n$,
--   $$
--   F^{\mathrm{bin}}_1(N)\le C\,n^{1/4}.
--   $$
--
--   This is the bottom of the contraction: iterating Lemma 4.4 from $F^{\mathrm{bin}}_m$ down to $F^{\mathrm{bin}}_1$ produces the exponent $-(m-1)/2+1/4$.
--
--   Differences from the source:
--   - reading: the standing hypotheses of §4 (p.20: |N − 2ⁿ| ≤ 2ⁿ/n), n otherwise unrestricted → 3 ≤ n together with |N − 2ⁿ| ≤ 2ⁿ/n; reason: §4 is the setting of Theorem 2, which assumes n ≥ 3, and the proof of Lemma 4.10 starts at 3 ≤ n; for n = 1 the slice decomposition of App. D.1 fails (N = 4 has the residue 3 of weight 2 = n + 1)
--   - encoding: F^bin_1(N) ≪ … (implied absolute constant) → ∃ C : ℝ, chosen before every other variable; reason: the paper's ≪ hides an absolute constant independent of n, N and the other parameters (§2.1, p.16)
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.6, p.22

import Mathlib
import Definitions.Def_HWMaskLeak_energyBin

namespace HWMaskLeak

/-- **Lemma 4.6 (The model `F₁` base case)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.6, p.22): uniformly for
`|N − 2ⁿ| ⩽ 2ⁿ/n`, `F^bin_1(N) ≪ n^{1/4}`.

**Formalization Note** `≪` is an absolute constant `C`, chosen before `n` and `N`; `n ⩾ 3` as in
Theorem 2; `n^{1/4}` is a real power. -/
theorem lemma_4_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) [NeZero N], 3 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n →
      energyBin n N 1 ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) := by sorry

end HWMaskLeak
