-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_Supplement_theorem_5_1
-- name    : InvMarketMaking.LOB.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:32:27.094307+00:00
-- url     : https://prove2.me/theorems/5924c0f1-c884-4799-b449-b844c684b134
-- title:
--   Theorem 5.1 — Algorithm 1 (two-bit) always posts $B_t<A_t$
-- statement:
--   Let $T\ge1$ and $\delta\in(0,1)$, and run Algorithm 1 (the Two-Bit Market Maker with subroutines Algorithms 2–3) on the grids $\mathcal B^\circ=\{n/\lfloor T^{1/3}\rfloor:0\le n<\lfloor T^{1/3}\rfloor\}$ and $\mathcal A^\circ=\{n/\lfloor T^{1/3}\rfloor:1\le n\le\lfloor T^{1/3}\rfloor\}$. Then for every valuation sequence, every argmax tie-break rule and every round $t\in\{1,\dots,T\}$, the posted pair satisfies
--   $$
--   B_t<A_t .
--   $$
--   So the two-bit algorithm only ever posts admissible bid–ask pairs. The pairs it posts are $(b,a')$ with $a'$ compatible with $b$, $(0,a')$ or $(b,1)$ after a halt, and the no-trade pair $(0,1)$.
--
--   Differences from the source:
--   - reading: a′ ← argmax{S^up_ℓ(a) : a ∈ C_ℓ(b)}, b′ ← argmax{F^up_ℓ(b) : b ∈ C_ℓ(a)}, no tie-break → an arbitrary argmax selection rule sel, quantified universally (IsArgmaxRule sel); reason: the page leaves ties open; the universal statement covers every tie-break
--   - reading: 'for b ∈ B_ℓ do … for a ∈ A_ℓ do' (Lines 7–13), order within each set unspecified → bid calls in increasing price order, then ask calls in increasing price order; reason: the page fixes bids before asks but no order within a set; every call uses only phase-ℓ quantities, so the order changes only which rounds a call occupies
--   - reading: no rule when no price remains active (B_ℓ = ∅) → Algorithm 1 posts (0, 1) from then on, as in footnote 4's fallback; reason: no call can be made; (0, 1) is the no-trade pair the paper uses for every fallback; on the good event (b°, a°) stays active
--   - encoding: 'at any t ∈ [T], Algorithm 1 selects (B_t, A_t) such that B_t < A_t' → for every valuation sequence vs, vb and every t ∈ [T], (twoBitMaker T δ sel vs vb t).1 < .2; reason: Algorithm 1 is deterministic given the valuations; the proof (p. 25) is pathwise
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Theorem 5.1, p. 24

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_Supplement_twoBitMaker

namespace InvMarketMaking.LOB.Supplement

/-- **Theorem 5.1** (Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market
Making Under Inventory Constraints, arXiv:2610.24562v1, p. 24). At any `t ∈ [T]`, Algorithm 1 selects
`(B_t, A_t)` such that `B_t < A_t`.

**Formalization Note** The statement is pathwise: it holds for every valuation sequence, every argmax
tie-break rule, every `T ≥ 1` and every `δ ∈ (0, 1)`. Algorithm 1 is `twoBitMaker` (Algorithms 1–3,
Eqs. (8)–(9), footnote 4), with calls in increasing price order and `(0, 1)` posted once no price is
active. -/
theorem theorem_5_1 (T : ℕ) (hT : 1 ≤ T) (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 1)
    (sel : Finset ℝ → (ℝ → ℝ) → ℝ) (hsel : IsArgmaxRule sel) (vs vb : ℕ → ℝ) :
    ∀ t ∈ Finset.Icc 1 T,
      (twoBitMaker T δ sel vs vb t).1 < (twoBitMaker T δ sel vs vb t).2 := by sorry

end InvMarketMaking.LOB.Supplement
