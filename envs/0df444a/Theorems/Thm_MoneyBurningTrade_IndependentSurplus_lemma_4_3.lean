-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_lemma_4_3
-- name    : MoneyBurningTrade.IndependentSurplus.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:48.684074+00:00
-- url     : https://prove2.me/theorems/45cfb4d9-f1f4-40bf-a4b3-5b9df462f663
-- title:
--   Lemma 4.3 — weak-budget-balance construction
-- statement:
--   Let $n\ge2$ and $0=q_0<\cdots<q_n=1$, with minimum gap $L$. For $0<\tau<L/2$, define the thresholds, rounding indices and growth factor $\Gamma$ by (16)–(17), and use the normalized payments of Appendix A.2. This concrete mechanism is measurable, DSIC, IR and WBB on the full report interval $[0,1]$, with allocation
--
--   $$x(s,b)=\begin{cases}0&\iota_S(s)\ge\iota_B(b),\\\Gamma^{\iota_B(b)-\iota_S(s)-1}/\Gamma^{n-1}&\iota_S(s)<\iota_B(b).\end{cases}$$
--
--   Every denominator in (17) is positive, $\Gamma>1$, and
--
--   $$x(s,b)\ge\Gamma^{-(n-1)}\quad\text{whenever }\iota_S(s)<\iota_B(b).$$
--
--   The conclusion includes the transfer chain $0\le sx\le p_S\le p_B\le bx\le1$. This establishes the actual WBB mechanism used throughout the separation argument, rather than a certificate that assumes its validity.
--
--   Differences from the source:
--   - generalization: existence of a mechanism with allocation (18) → the concrete normalized mechanism from Appendix A.2, plus positivity of its growth factor and denominators and the transfer chain; reason: the source asserts only that some DSIC, IR, WBB mechanism has allocation (18); the Lean asserts this of the specific mechanism with the normalized payments of Appendix A.2 (the one later results call the mechanism of Lemma 4.3), together with well-definedness facts from the proof, which implies the source’s existential claim
--   - encoding: the source’s integer grid indices and finite extrema → natural indices with bounds, finite real extrema and signed integer exponents; reason: every extremum is over a finite nonempty set; bounds prevent truncated subtraction from changing an index or exponent
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.3; Appendix A.2, printed p. 23–24; proof 40–41 (PDF p. 24–25; proof 41–42); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_NormalizedMechanism
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsDSIC
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsIR
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_IsWBB

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Lemma 4.3, pp.23–24, using its actual normalized payments from Appendix A.2.
The concrete mechanism supplies the source's existential witness. -/
theorem lemma_4_3 (G : Grid) (hG : IsGrid G) (τ : ℝ)
    (hτ : 0 < τ) (hτgap : τ < minGap G / 2) :
    1 < growthFactor G τ ∧
    (∀ i j : ℕ, 1 ≤ i → i < j → j ≤ G.n →
      0 < G.q j - G.q (i - 1) - (if 1 < i then τ else 0) -
        (if j < G.n then τ else 0)) ∧
    IsMechanism reportInterval (normalizedMechanism G τ) ∧
    IsDSIC reportInterval (normalizedMechanism G τ) ∧
    IsIR reportInterval (normalizedMechanism G τ) ∧
    IsWBB reportInterval (normalizedMechanism G τ) ∧
    TransferBounds (normalizedMechanism G τ) ∧
    (∀ s ∈ reportInterval, ∀ b ∈ reportInterval,
      (normalizedMechanism G τ).x (s, b) =
        if sellerIndex G τ s < buyerIndex G τ b then
          growthFactor G τ ^ ((buyerIndex G τ b : ℤ) - (sellerIndex G τ s : ℤ) - 1) /
            growthFactor G τ ^ (G.n - 1)
        else 0) ∧
    (∀ s ∈ reportInterval, ∀ b ∈ reportInterval,
      sellerIndex G τ s < buyerIndex G τ b →
      growthFactor G τ ^ (-((G.n : ℤ) - 1)) ≤ (normalizedMechanism G τ).x (s, b)) := by sorry

end MoneyBurningTrade.IndependentSurplus
