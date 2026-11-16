-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_5_6
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:50.942858+00:00
-- url     : https://prove2.me/theorems/383e00be-4572-4b25-b8b3-40816b26aaa7
-- title:
--   Lemma 5.6 — first-best gains from trade under the laws (23)
-- statement:
--   Let $t\ge4$, $\lambda=1/(1-e^{-t})$, and let $F_s,F_b$ be the laws (23). The first-best gains from trade $\mathrm{GFT}_{\mathrm{OPT}}(F_s\times F_b)=\mathbb E[\max\{v_b-v_s,0\}]$ satisfy
--
--   $$\mathrm{GFT}_{\mathrm{OPT}}(F_s\times F_b)=\lambda^2\bigl((t-2)e^{-t}+(t+2)e^{-2t}\bigr)\ge\frac{\lambda^2te^{-t}}{2}.$$
--
--   Both the closed form and the lower bound are asserted. With Lemmas 5.3 and 5.4 this gives the ratio bound $\frac2t(1+\frac{11}{e}(\frac12+\log t))$ of Theorem 5.1.
--
--   **Formalization Note** $\mathrm{GFT}_{\mathrm{OPT}}$ is the published `SecondBestBT.firstBest`, the integral of $\max(v_b-v_s,0)$ over the product law.
--
--   Differences from the source:
--   - encoding: the fixed t ≥ 4 of the proof of Theorem 5.1, chosen with (24) → every real t ≥ 4; reason: the lemma does not involve ε and every t ≥ 4 meets (24) for some ε > 0; the same instances
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 5.6; §5.1; proof in Appendix A.11, printed p. 33 (PDF p. 34); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_ExponentialLaws
import Definitions.Def_SecondBestBT_firstBest

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 5.6, §5.1 p.33: for every `t ≥ 4`, under the laws (23),
`GFT_OPT(F_s × F_b) = λ²((t − 2)e^(−t) + (t + 2)e^(−2t)) ≥ λ² t e^(−t) / 2`.
Both the closed form and the lower bound. -/
theorem lemma_5_6 (t : ℝ) (ht : 4 ≤ t) :
    SecondBestBT.firstBest (bdSellerLaw t) (bdBuyerLaw t) =
      bdLambda t ^ 2 * ((t - 2) * Real.exp (-t) + (t + 2) * Real.exp (-2 * t)) ∧
    bdLambda t ^ 2 * t * Real.exp (-t) / 2 ≤
      bdLambda t ^ 2 * ((t - 2) * Real.exp (-t) + (t + 2) * Real.exp (-2 * t)) := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
