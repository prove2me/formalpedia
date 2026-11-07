-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_4_10
-- name    : HWMaskLeak.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:24.107592+00:00
-- url     : https://prove2.me/theorems/f7a194fe-c20b-4e0b-b616-fc1a8c276642
-- title:
--   Lemma 4.10 — Krawtchouk-type estimate for $\hat B_w(t)$
-- statement:
--   There is an absolute constant $C$ such that for every $n\ge3$, every $N$ with $|N-2^n|\le2^n/n$, every central weight $w\in W_{\mathrm{cent}}$ and every $0<t<N$,
--   $$
--   |\hat B_w(t)|\le C\,N^{-1}\binom nw\Bigl(\frac{|n-2w|}{n}+\frac1{\sqrt n}\Bigr).
--   $$
--
--   Summing its square against $\rho_w(N)^{-1}$ over the central weights gives the $O(1/n)$ bound of Lemma 4.5.
--
--   Differences from the source:
--   - reading: the standing hypotheses of §4 (p.20: |N − 2ⁿ| ≤ 2ⁿ/n), n otherwise unrestricted → 3 ≤ n together with |N − 2ⁿ| ≤ 2ⁿ/n; reason: §4 is the setting of Theorem 2, which assumes n ≥ 3, and the proof of Lemma 4.10 starts at 3 ≤ n; for n = 1 the slice decomposition of App. D.1 fails (N = 4 has the residue 3 of weight 2 = n + 1)
--   - encoding: |B̂_w(t)| ≪ … (implied absolute constant) → ∃ C : ℝ, chosen before every other variable; reason: the paper's ≪ hides an absolute constant independent of n, N and the other parameters (§2.1, p.16)
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.10, p.24

import Mathlib
import Definitions.Def_HWMaskLeak_fullRange
import Definitions.Def_HWMaskLeak_Wcent

namespace HWMaskLeak

/-- **Lemma 4.10 (Krawtchouk-type estimate)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.10, p.24): under the standing hypotheses
of §4 (`|N − 2ⁿ| ⩽ 2ⁿ/n`), for every `w ∈ W_cent` and `0 < t < N`,
`|B̂_w(t)| ≪ N^{−1} (n choose w) (|n − 2w|/n + 1/√n)`.

**Formalization Note** `≪` is an absolute constant `C`, chosen before `n, N, w, t`; `n ⩾ 3` as in
Theorem 2 and in the proof ("For 3 ⩽ n < 9 …", p.24). -/
theorem lemma_4_10 :
    ∃ C : ℝ, ∀ (n N : ℕ) [NeZero N], 3 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n →
      ∀ w ∈ Wcent n, ∀ t : ZMod N, t ≠ 0 →
        ‖fullRangeHat n N w t‖ ≤
          C * ((N : ℝ)⁻¹ * (n.choose w : ℝ) * (|(n : ℝ) - 2 * w| / n + 1 / Real.sqrt n)) := by sorry

end HWMaskLeak
