-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_13
-- name    : HopfieldPSpin.Shattering.lemma_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:32.209042+00:00
-- url     : https://prove2.me/theorems/ae11b034-b138-4497-a838-4ad315ccc147
-- title:
--   Lemma 4.13 — explicit large-$p$ soft gap $g_{p,\beta}(r_p,R_p)\ge\varepsilon r_p\log p>0$
-- statement:
--   Fix $\varepsilon\in(0,1)$ and let $\delta=\varepsilon/4$, $r_p=1/(2p^{1+\delta})$, $R_p=\varepsilon/(8p)$. There is $p_0=p_0(\varepsilon)$ such that for all $p\ge p_0$, $2r_p<R_p<1/2$, and every $\beta\ge(1+\varepsilon)\sqrt{2\log p/p}$ satisfies
--   $$g_{p,\beta}(r_p,R_p)\ge\varepsilon\,r_p\log p>0 .$$
--   It verifies the gap hypothesis of Proposition 4.15 in the window of Theorem 2.2.
--
--   Differences from the source: none.
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 32 (PDF 34), Lemma 4.13, (4.52)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Entropy

namespace HopfieldPSpin.Shattering

/-- Lemma 4.13 (p. 32): for `ε ∈ (0, 1)` there is `p₀(ε)` such that for all `p ≥ p₀`,
`2 r_p < R_p < 1/2` and every `β ≥ (1 + ε) √(2 log p / p)` satisfies
`g_{p,β}(r_p, R_p) ≥ ε r_p log p > 0`. -/
theorem lemma_4_13 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀ ≤ p →
      2 * radiusR ε p < radiusBigR ε p ∧ radiusBigR ε p < 1 / 2 ∧
      ∀ β : ℝ, (1 + ε) * Real.sqrt (2 * Real.log p / p) ≤ β →
        ε * radiusR ε p * Real.log p ≤ gapG p β (radiusR ε p) (radiusBigR ε p) ∧
        0 < ε * radiusR ε p * Real.log p := by sorry

end HopfieldPSpin.Shattering
