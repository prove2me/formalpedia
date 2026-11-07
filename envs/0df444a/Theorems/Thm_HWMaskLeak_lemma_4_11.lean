-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_4_11
-- name    : HWMaskLeak.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:38.032515+00:00
-- url     : https://prove2.me/theorems/40ebf807-8644-4483-b573-a923b607024a
-- title:
--   Lemma 4.11 — the integral $I\ll|1-2p|/\sqrt n+1/n$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $n\ge9$, let $N$ satisfy $|N-2^n|\le2^n/n$, let $0<t<N$, let $w\in W_{\mathrm{cent}}$, put $p=w/n$ and $\varphi_j=\{2^jt/N\}$. Then
--   $$
--   I=\int_{-\pi}^{\pi}\prod_{j=0}^{n-1}\bigl|(1-p)+p\exp(\imath\theta+\imath\cdot2\pi\varphi_j)\bigr|\,d\theta\le C\Bigl(\frac{|1-2p|}{\sqrt n}+\frac1n\Bigr).
--   $$
--
--   With the Cauchy bound and Stirling's formula this gives Lemma 4.10 for $n\ge9$.
--
--   Differences from the source:
--   - encoding: I ≪ … (implied absolute constant) → ∃ C : ℝ, chosen before every other variable; reason: the paper's ≪ hides an absolute constant independent of n, N and the other parameters (§2.1, p.16)
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.11, p.24

import Mathlib
import Definitions.Def_HWMaskLeak_Wcent
import Definitions.Def_HWMaskLeak_PJ

namespace HWMaskLeak

/-- **Lemma 4.11** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), Lemma 4.11, p.24): for `n ⩾ 9`, `0 < t < N`, `|N − 2ⁿ| ⩽ 2ⁿ/n`,
`w ∈ W_cent` and `φ_j = {2ʲt/N}`, with `p = w/n`,
`I = ∫_{−π}^{π} Π_{j=0}^{n−1} |(1 − p) + p exp(ıθ + ı·2πφ_j)| dθ ≪ |1 − 2p|/√n + 1/n`.

**Formalization Note** `≪` is an absolute constant `C`, chosen before `n, N, t, w`; `φ_j` is
`phi N t j`, the fractional part of `2ʲ · t.val / N`. -/
theorem lemma_4_11 :
    ∃ C : ℝ, ∀ (n N : ℕ) [NeZero N], 9 ≤ n → |(N : ℝ) - 2 ^ n| ≤ 2 ^ n / n →
      ∀ t : ZMod N, t ≠ 0 → ∀ w ∈ Wcent n,
        ∫ θ in (-Real.pi)..Real.pi, ∏ j ∈ Finset.range n,
            ‖((1 - (w : ℝ) / n : ℝ) : ℂ) + (((w : ℝ) / n : ℝ) : ℂ) *
              Complex.exp ((θ : ℂ) * Complex.I + ((2 * Real.pi * phi N t j : ℝ) : ℂ) * Complex.I)‖ ≤
          C * (|1 - 2 * ((w : ℝ) / n)| / Real.sqrt n + 1 / n) := by sorry

end HWMaskLeak
