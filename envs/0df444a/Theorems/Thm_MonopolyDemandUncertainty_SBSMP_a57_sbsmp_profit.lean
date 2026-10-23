-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_a57_sbsmp_profit
-- name    : MonopolyDemandUncertainty.SBSMP.a57_sbsmp_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:35.821864+00:00
-- url     : https://prove2.me/theorems/8f6a0e70-e2dd-4a0a-9b05-a2b88bd652fe
-- title:
--   §A.5.7, closing display, p. 17 (PDF 18) — SBSMP(a, b) earns α1D1(a)a + α2D2(b)b, uniquely maximized at the monopoly prices, and is BIC and EIR
-- statement:
--   Consider the two-state monopoly economy with the standing assumptions and Conditions 1 and 3, and let $p_1^m, p_2^m$ be monopoly prices, i.e. maximizers of $p\,D_1(p)$ and $p\,D_2(p)$ over $p \in V$.
--
--   1. For all posted prices $a, b \in V$, the state-by-state posted-price mechanism with price $a$ in state 1 and $b$ in state 2 earns
--   $$\pi(a,b) = \alpha_1 D_1(a)\,a + \alpha_2 D_2(b)\,b.$$
--   2. For all $a, b \in V$, $\pi(a,b) \le \pi(p_1^m, p_2^m)$, with equality only if $a = p_1^m$ and $b = p_2^m$.
--   3. The mechanism with prices $(p_1^m, p_2^m)$ (SBSMP) is BIC and EIR.
--
--   This is the closing computation of the proof of Proposition 1: once the optimal mechanism is known to be a pair of posted prices, the optimal prices are the monopoly prices, and they are unique.
--
--   **Formalization Note** Monopoly prices are maximizers on $V$ rather than roots of the first-order condition, so the statement is not vacuous when the maximum sits at $\underline v$.
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 17, §A.5.7, closing display

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- §A.5.7, closing display, p. 17 (PDF 18). (a) For posted prices `a, b ∈ V`, the profit of
`sbsmp a b` is `α₁ D₁(a) a + α₂ D₂(b) b`. (b) Under Conditions 1 and 3 it is maximized exactly at
the monopoly prices `(p₁, p₂)` (maximizers of `p D_i(p)` on `V`), uniquely. (c) `sbsmp p₁ p₂` is
BIC and EIR. Paper's states 1, 2 = indices `0`, `1`. -/
theorem a57_sbsmp_profit (E : Economy) (hE : E.Valid) (h1 : E.Condition1) (h3 : E.Condition3)
    (p₁ p₂ : ℝ) (hp₁ : E.IsMonopolyPrice 0 p₁) (hp₂ : E.IsMonopolyPrice 1 p₂) :
    (∀ a ∈ E.V, ∀ b ∈ E.V,
        E.profit (sbsmp a b) = E.α₁ * E.D 0 a * a + (1 - E.α₁) * E.D 1 b * b) ∧
      (∀ a ∈ E.V, ∀ b ∈ E.V, E.profit (sbsmp a b) ≤ E.profit (sbsmp p₁ p₂) ∧
        (E.profit (sbsmp a b) = E.profit (sbsmp p₁ p₂) → a = p₁ ∧ b = p₂)) ∧
      E.IsBIC (sbsmp p₁ p₂) ∧ E.IsEIR (sbsmp p₁ p₂) := by sorry
end MonopolyDemandUncertainty.SBSMP
