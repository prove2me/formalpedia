-- Prove2me | Theorems.Thm_MultiItemRev_Decomp_theorem_7
-- name    : MultiItemRev.Decomp.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:32.256978+00:00
-- url     : https://prove2.me/theorems/dcb11778-e80e-4c7e-8134-b5ec5fa73a32
-- title:
--   Theorem 7, p. 18 — for independent Y, Z: Rev(Y,Z) ≤ Rev(Y)+Rev(Z)+BRev(Y)+BRev(Z) ≤ 2(Rev(Y)+Rev(Z))
-- statement:
--   **Theorem 7 (decomposition).** Let $Y$ be a nonnegative random valuation for $k_1 \ge 1$ goods and $Z$ one for $k_2 \ge 1$ goods, with arbitrary dependence among the coordinates of $Y$ and among those of $Z$. If $Y$ and $Z$ are independent, then
--   $$
--   \mathrm{Rev}(Y, Z) \le \mathrm{Rev}(Y) + \mathrm{Rev}(Z) + \mathrm{BRev}(Y) + \mathrm{BRev}(Z) \qquad (6)
--   $$
--   $$
--   \le 2\,\big(\mathrm{Rev}(Y) + \mathrm{Rev}(Z)\big). \qquad (7)
--   $$
--
--   Here $\mathrm{Rev}(Y, Z)$ is the optimal revenue from selling all $k_1 + k_2$ goods together. The theorem says that, for independent groups of goods, selling each group optimally on its own loses at most half of the optimal revenue. For one-dimensional $Y$ and $Z$ both inequalities reduce to Theorem A, and Theorems C and D are proved from it by induction on the number of goods.
--
--   **Formalization Note** Valuations are represented by their laws; independence is encoded by taking the law of $(Y,Z)$ on $\mathbb{R}^{k_1+k_2}_+$ to be the product of the laws of $Y$ and $Z$. All revenues take values in $[0,\infty]$, and both inequalities are stated, with the same middle term.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 18, Theorem 7, (6) and (7)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.Decomp

theorem theorem_7 {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₁] [Nonempty ι₂]
    (μY : Measure (ι₁ → ℝ≥0)) (μZ : Measure (ι₂ → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] :
    Rev (jointLaw μY μZ) ≤ Rev μY + Rev μZ + BRev μY + BRev μZ ∧
      Rev μY + Rev μZ + BRev μY + BRev μZ ≤ 2 * (Rev μY + Rev μZ) := by sorry

end MultiItemRev.Decomp
