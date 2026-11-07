-- Prove2me | Theorems.Thm_HWMaskLeak_lemma_C_4
-- name    : HWMaskLeak.lemma_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:29:40.541456+00:00
-- url     : https://prove2.me/theorems/c25ca3a4-e5f2-427f-8f11-2082d6e969bf
-- title:
--   Lemma C.4 — dispersion lemma $\sum_{j<n}\sin^2(\alpha+2^j\beta)\ge\frac{n-1}{10}\sin^2\alpha$
-- statement:
--   For every integer $n\ge0$ and all real $\alpha,\beta$,
--   $$
--   S_n(\alpha,\beta):=\sum_{j=0}^{n-1}\sin^2\bigl(\alpha+2^j\beta\bigr)\ge\frac{n-1}{10}\sin^2\alpha.
--   $$
--
--   Successive angles of the doubling orbit cannot all stay near $0$ unless $\alpha$ is; this quantitative form gives the Gaussian decay $\exp(-cn\theta^2)$ in Lemma 4.11.
--
--   Differences from the source:
--   - encoding: any n → n : ℕ with n − 1 computed in ℝ; reason: for n = 0 the bound is −sin²α/10 ≤ 0, as on the page
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. C.5, Lemma C.4, p.50

import Mathlib

namespace HWMaskLeak

/-- **Lemma C.4 (Dispersion Lemma)** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. C.5, Lemma C.4, p.50): for any `n, α, β`,
`S_n(α, β) := Σ_{j=0}^{n−1} sin²(α + 2ʲβ) ⩾ ((n − 1)/10) sin² α`.

**Formalization Note** `n` is a natural number and `α, β` are real; `n − 1` is computed in `ℝ`. -/
theorem lemma_C_4 (n : ℕ) (α β : ℝ) :
    ((n : ℝ) - 1) / 10 * Real.sin α ^ 2 ≤ ∑ j ∈ Finset.range n, Real.sin (α + 2 ^ j * β) ^ 2 := by sorry

end HWMaskLeak
