-- Prove2me | Theorems.Thm_MCAListDecoding_PowersGenerator_lemma_B_1
-- name    : MCAListDecoding.PowersGenerator.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:18:09.823257+00:00
-- url     : https://prove2.me/theorems/d5d4eff9-bc46-4ff4-ad9c-4c25d17ef6b8
-- title:
--   Lemma B.1 — numerical estimate (J_h(δ_C)/δ_C)(11/5 + X) ≤ 31/5
-- statement:
--   Let $\delta\in(0,1]$ (the relative distance $\delta_C$) and $\gamma\ge0$ satisfy (3): $1-\gamma>\max\{(1-\delta)^{1/3},\ \tfrac12(1+(1-\delta))\}$, and let $h=d+2$ with $d\ge1$. Let $\tau\in\big(1-\delta,\ \frac{1-\gamma+\sqrt{1-\delta}}2\big]$ and $X=\frac{\tau-(1-\delta)}{\tau(1-\gamma-\tau)}$. Then
--   $$\frac{J_h(\delta)}{\delta}\Big(\frac{11}5+X\Big)\le\frac{31}5 .$$
--
--   Differences from the source:
--   - generalization: δ = δ_C of a code and γ = e/n in the setting of Theorem 7.1, h = d + 2 → arbitrary reals δ ∈ (0,1], γ ≥ 0 satisfying (3): 1 − γ > max{(1−δ)^{1/3}, (1+(1−δ))/2}, and h = d + 2 with d ≥ 1; reason: the estimate is purely numerical and its proof uses only (3) and h ≥ 3; the setting of Theorem 7.1 gives these hypotheses, so the Lean statement specializes to the source
-- source:
--   Manzur, Mutual Correlated Agreement and List-Decoding: Improvements and Separations, STOC 2027 submission (manuscript of 2026-11-03, sha256 1357b300…), Lemma B.1, p. 75 (inequality (3), p. 29)

import Mathlib
import Definitions.Def_MCAListDecoding_PowersGenerator_Code

namespace MCAListDecoding.PowersGenerator

/-- Lemma B.1 (numerical estimate), p. 75, for reals `δ ∈ (0, 1]` (the relative distance `δ_C`)
and `γ ≥ 0` satisfying inequality (3), `1 - γ > max{(1 - δ)^{1/3}, (1 + (1 - δ))/2}`, and
`h = d + 2` with `d ≥ 1`. For `τ ∈ (1 - δ, (1 - γ + √(1 - δ))/2]` and
`X = (τ - (1 - δ))/(τ (1 - γ - τ))`, `(J_h(δ)/δ)(11/5 + X) ≤ 31/5`. -/
theorem lemma_B_1 (d : ℕ) (hd : 1 ≤ d) (δ γ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ : 0 ≤ γ)
    (h3 : max ((1 - δ) ^ ((1 : ℝ) / 3)) ((1 + (1 - δ)) / 2) < 1 - γ)
    (τ : ℝ) (hτ0 : 1 - δ < τ) (hτ1 : τ ≤ (1 - γ + Real.sqrt (1 - δ)) / 2) :
    johnsonRadius (d + 2) δ / δ * (11 / 5 + (τ - (1 - δ)) / (τ * (1 - γ - τ))) ≤
      31 / 5 := by sorry

end MCAListDecoding.PowersGenerator
