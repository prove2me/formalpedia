-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_A_1
-- name    : MCAListDecoding.PowersGenerator.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:17:25.545235+00:00
-- url     : https://prove2.me/theorems/690322c9-13dd-4717-a3bd-9be9494cec53
-- title:
--   Lemma A.1 — (τ−(1−δ_C))/(τ²−(1−δ_C)) < 5 at τ = (1−γ+√(1−δ_C))/2, so at most 4 large curves
-- statement:
--   Let $\delta\in(0,1]$ (the relative distance $\delta_C$) and $\gamma\ge0$ satisfy (3): $1-\gamma>\max\{(1-\delta)^{1/3},\ \tfrac12(1+(1-\delta))\}$. With $\tau=\frac{1-\gamma+\sqrt{1-\delta}}2$,
--   $$\frac{\tau-(1-\delta)}{\tau^2-(1-\delta)}<5 .$$
--   Consequently the integer number of curves in Lemma 4.11 is at most $4$.
--
--   Differences from the source:
--   - generalization: δ = δ_C of a code and γ = e/n in the setting of Lemma 4.11 → arbitrary reals δ ∈ (0,1], γ ≥ 0 satisfying (3): 1 − γ > max{(1−δ)^{1/3}, (1+(1−δ))/2}; reason: the estimate is purely numerical and its proof uses only (3); the setting of Lemma 4.11 gives these hypotheses (by (3), p. 29), so the Lean statement specializes to the source
--   - encoding: the integer number of curves in Lemma 4.11 is at most 4 → every natural number L with L ≤ (τ−(1−δ))/(τ²−(1−δ)) satisfies L ≤ 4; reason: Lemma 4.11 bounds that number by this ratio; the 'consequently' clause is the integer consequence
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma A.1, p. 74 (inequality (3), p. 29)

import Mathlib

namespace MCAListDecoding.PowersGenerator

/-- Lemma A.1, p. 74 (numerical estimate for Lemma 4.11), for reals `δ ∈ (0, 1]` (the relative
distance `δ_C`) and `γ ≥ 0` satisfying inequality (3),
`1 - γ > max{(1 - δ)^{1/3}, (1 + (1 - δ))/2}`. With `τ = (1 - γ + √(1 - δ))/2`,
`(τ - (1 - δ))/(τ² - (1 - δ)) < 5`; consequently every natural number bounded by this ratio
(the number of curves in Lemma 4.11) is at most `4`. -/
theorem lemma_A_1 (δ γ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ : 0 ≤ γ)
    (h3 : max ((1 - δ) ^ ((1 : ℝ) / 3)) ((1 + (1 - δ)) / 2) < 1 - γ) :
    ((1 - γ + Real.sqrt (1 - δ)) / 2 - (1 - δ)) /
        (((1 - γ + Real.sqrt (1 - δ)) / 2) ^ 2 - (1 - δ)) < 5 ∧
      ∀ L : ℕ, (L : ℝ) ≤ ((1 - γ + Real.sqrt (1 - δ)) / 2 - (1 - δ)) /
          (((1 - γ + Real.sqrt (1 - δ)) / 2) ^ 2 - (1 - δ)) → L ≤ 4 := by sorry

end MCAListDecoding.PowersGenerator
