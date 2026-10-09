-- Prove2me | Theorems.Thm_MultiItemRev_MultiBuyer_display_21
-- name    : MultiItemRev.MultiBuyer.display_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:12.962491+00:00
-- url     : https://prove2.me/theorems/dc8ef343-89ce-4b83-9421-bf6955c7d785
-- title:
--   (21), p. 50 — z⁽¹⁾ P[Y⁽¹⁾ ≥ z⁽¹⁾] ≤ Rev^DS(Y) for one good and n buyers
-- statement:
--   Let $Y = (Y^1, \dots, Y^n) \in \mathbb R^n_+$ be the random vector of the values of $n \ge 1$ buyers for a single good (arbitrarily correlated), and write $Y^{(1)} = \max_j Y^j$. For every $t \ge 0$,
--   $$t\,\mathbb P\big[Y^{(1)} \ge t\big] \le \mathrm{Rev}^{DS}(Y).$$
--
--   In the paper $t = z^{(1)}$, the highest value of the buyers for the second good. The bound is the revenue of posting the price $t$ and selling the good to a buyer whose value is at least $t$, if there is one; this is the second of the two terms in the proof of display (19).
--
--   **Formalization Note** One good is `ι = Unit`, and the one-good profile law is `oneGoodN μY`. The product $t \cdot \mathbb P[\cdot]$ is taken in $[0,\infty]$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 50, display (21), proof of Theorems 33 and 34

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-- Display (21), p. 50: for one good with value vector `Y ∈ ℝ^n_+` and any `z^{(1)} ≥ 0`,
`z^{(1)} P[Y^{(1)} ≥ z^{(1)}] ≤ Rev^{DS}(Y)`, where `Y^{(1)} = max_j Y^j`. -/
theorem display_21 {n : ℕ} (hn : 1 ≤ n) (μY : Measure (Fin n → ℝ≥0)) [IsProbabilityMeasure μY]
    (t : ℝ≥0) :
    (t : ℝ≥0∞) * μY {y | t ≤ maxCoord y} ≤ RevDS (oneGoodN μY) := by sorry

end MultiItemRev.MultiBuyer
