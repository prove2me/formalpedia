-- Prove2me | Theorems.Thm_MoneyBurningTrade_IndependentSurplus_Supplement_lemma_4_9
-- name    : MoneyBurningTrade.IndependentSurplus.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:37:53.299794+00:00
-- url     : https://prove2.me/theorems/96548682-c13d-463a-a1e0-7236323d40d3
-- title:
--   Lemma 4.9 — the grid (22) satisfies the grid condition (19)
-- statement:
--   Let $n\ge4$, $\delta=1/(100n)$, and let $0=q_0<q_1<\dots<q_n=1$ be the grid of equation (22), $q_i=(\delta^{n-i}-\delta^n)/(1-\delta^n)$. Then the grid condition (19) of Definition 4.4 holds with this $\delta$:
--
--   $$q_{j-1}-q_i\le4\delta\,(q_j-q_{i-1})\qquad\text{for all }1\le i<j\le n.$$
--
--   Together with a small enough slack $\tau$, this makes the grid (22) a separation grid, so that Lemma 4.5 applies in the proof of Theorem 4.2.
--
--   Differences from the source:
--   - encoding: the fixed integer n ≥ 4 of §4.3, chosen with (n − 3)/16 ≥ 1/ε → every natural number n ≥ 4; reason: the lemma does not involve ε and every n ≥ 4 meets the side condition for some ε > 0; the same instances
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.9; proof in Appendix A.6, printed p. 31 (PDF p. 32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_CorrelatedGrid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- Lemma 4.9, §4.3 p.31: for every `n ≥ 4`, the grid (22) with `δ = 1/(100n)`
satisfies the grid condition (19) of Definition 4.4 (constant 4, all `1 ≤ i < j ≤ n`). -/
theorem lemma_4_9 (n : ℕ) (hn : 4 ≤ n) :
    gridCondition (correlatedGrid n) (corrDelta n) := by sorry

end MoneyBurningTrade.IndependentSurplus.Supplement
