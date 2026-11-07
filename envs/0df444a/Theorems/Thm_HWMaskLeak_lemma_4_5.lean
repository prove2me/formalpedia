-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_4_5
-- name    : HWMaskLeak.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:07.084274+00:00
-- url     : https://prove2.me/theorems/1dccd8b8-6dfa-43dc-aec2-f8343dd616ec
-- title:
--   Lemma 4.5 — key spectral estimate $\alpha_{\mathrm{bin}}(N)\ll n^{-1}$
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge3$ and every $N$ with $|N-2^n|\le2^n/n$,
--   $$
--   \alpha_{\mathrm{bin}}(N)\le\frac Cn.
--   $$
--
--   All arithmetic difficulty of the near-dyadic upper bound sits in this estimate: it replaces the exact rotation symmetry of Mersenne moduli by a quantitative dispersion along the doubling orbit $\{2^jt/N\}$.
--
--   Differences from the source:
--   - reading: the standing hypotheses of §4 (p.20: |N − 2ⁿ| ≤ 2ⁿ/n), n otherwise unrestricted → 3 ≤ n together with |N − 2ⁿ| ≤ 2ⁿ/n; reason: §4 is the setting of Theorem 2, which assumes n ≥ 3, and the proof of Lemma 4.10 starts at 3 ≤ n; for n = 1 the slice decomposition of App. D.1 fails (N = 4 has the residue 3 of weight 2 = n + 1)
--   - encoding: α_bin(N) ≪ … (implied absolute constant) → ∃ C : ℝ, chosen before every other variable; reason: the paper's ≪ hides an absolute constant independent of n, N and the other parameters (§2.1, p.16)
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.5, p.21

import Mathlib
import Definitions.Def_HWMaskLeak_alphaBin

namespace HWMaskLeak

/-- **Lemma 4.5 (Key spectral estimate)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.5, p.21): for `|N − 2ⁿ| ⩽ 2ⁿ/n`,
`α_bin(N) ≪ n^{−1}`.

**Formalization Note** `≪` is an absolute constant `C`, chosen before `n` and `N`; `n ⩾ 3` as in
Theorem 2. -/
theorem lemma_4_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) [NeZero N], 3 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n →
      alphaBin n N ≤ C / n := by sorry

end HWMaskLeak
