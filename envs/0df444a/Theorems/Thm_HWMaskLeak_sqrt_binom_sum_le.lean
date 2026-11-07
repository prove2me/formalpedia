-- Prove2me | Theorems.Thm_HWMaskLeak_sqrt_binom_sum_le
-- name    : HWMaskLeak.sqrt_binom_sum_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:30:20.256567+00:00
-- url     : https://prove2.me/theorems/abdc75be-c65e-4585-8b68-5621cb425ce7
-- title:
--   App. B.3 — $\sum_w\sqrt{\binom nw2^{-n}}\le\sqrt5+\sqrt{5\pi/2}\,n^{1/4}$
-- statement:
--   For every integer $n\ge1$, with $p_w:=\binom nw2^{-n}$,
--   $$
--   \sum_{0\le w\le n}\sqrt{p_w}\le\sqrt5+\sqrt{5\pi/2}\;n^{1/4}.
--   $$
--
--   This explicit estimate is the input of the $F_1$ bound (Lemma 3.4) and of the model base case (Lemma 4.6, App. C.3).
--
--   Differences from the source:
--   - reading: the display chain Σ√p_w ≤ … ≤ √5 + √(5π/2)·n^{1/4} ≪ n^{1/4} → the inequality between the chain's first member and its explicit last bound, for every n ≥ 1; reason: the intermediate members are steps of the proof; a_w = 1 + (w − n/2)²/n requires n ≥ 1
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), App. B.3 (proof of Lemma 3.4), p.43, display chain

import Mathlib

namespace HWMaskLeak

/-- **The binomial square-root estimate of App. B.3** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight: From Additive Sharing to
Learning with Physical Rounding*, preprint (version of October 31, 2026, sha256 ab686360…), App. B.3 (proof of Lemma 3.4), display
chain, p.43): with `p_w := (n choose w) 2^{−n}`,
`Σ_{0 ⩽ w ⩽ n} √p_w ⩽ √5 + √(5π/2) · n^{1/4}`.

**Formalization Note** Stated for every `n ⩾ 1` (the chain divides by `n`); `n^{1/4}` is a real
power. -/
theorem sqrt_binom_sum_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ w ∈ Finset.range (n + 1), Real.sqrt ((n.choose w : ℝ) * ((2 : ℝ) ^ n)⁻¹) ≤
      Real.sqrt 5 + Real.sqrt (5 * Real.pi / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) := by sorry

end HWMaskLeak
