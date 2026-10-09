-- Prove2me | Theorems.Thm_MultiItemRev_MultiBuyer_theorem_33
-- name    : MultiItemRev.MultiBuyer.theorem_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:06.436553+00:00
-- url     : https://prove2.me/theorems/51ba19d8-3cc6-45f4-9aeb-a73ef515213f
-- title:
--   Theorem 33, p. 49 — n buyers, two independent goods, DS: Rev^DS(X₁) + Rev^DS(X₂) ≥ ½ Rev^DS(X₁, X₂)
-- statement:
--   Consider one seller, $n \ge 1$ buyers and two goods. Let $X_1 = (X^j_1)_{j=1,\dots,n}$ and $X_2 = (X^j_2)_{j=1,\dots,n}$ be the random vectors in $\mathbb R^n_+$ of the buyers' values for good 1 and for good 2. Assume $X_1$ and $X_2$ are **independent**; the buyers' values $X^1_i, \dots, X^n_i$ for the same good may be arbitrarily correlated. Then, under dominant strategy implementation, selling each good separately with its optimal one-good mechanism guarantees at least half the optimal revenue:
--   $$\mathrm{Rev}^{DS}(X_1) + \mathrm{Rev}^{DS}(X_2) \ge \tfrac12\,\mathrm{Rev}^{DS}(X_1, X_2).$$
--
--   Here $\mathrm{Rev}^{DS}$ is the supremum of the seller's expected revenue over feasible ($\sum_j q^j_i \le 1$), dominant-strategy incentive compatible and individually rational mechanisms. This is the dominant-strategy half of Theorem 18 of the paper, and the $n$-buyer generalization of Theorem A.
--
--   **Formalization Note** The law of $(X_1, X_2)$ is `twoGoodsN μY μZ`, the image of the product law $\mu_Y \otimes \mu_Z$, which encodes exactly the independence of the two goods. The inequality is stated in $[0,\infty]$ with the constant $\tfrac12$ as printed; both sides may be $+\infty$.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 49, Theorem 33 (see also p. 29, Theorem 18 and Remark (a))

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-- Theorem 33, p. 49: with `n` buyers, two goods and dominant strategy implementation, if the value
vectors `X_1 = (X^j_1)_j` and `X_2 = (X^j_2)_j` of the two goods are independent (the buyers being
arbitrarily correlated within each good), then
`Rev^{DS}(X_1) + Rev^{DS}(X_2) ≥ (1/2) Rev^{DS}(X_1, X_2)`. -/
theorem theorem_33 (n : ℕ) (hn : 1 ≤ n) (μY μZ : Measure (Fin n → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    (1 / 2 : ℝ≥0∞) * RevDS (twoGoodsN μY μZ) ≤ RevDS (oneGoodN μY) + RevDS (oneGoodN μZ) := by sorry

end MultiItemRev.MultiBuyer
