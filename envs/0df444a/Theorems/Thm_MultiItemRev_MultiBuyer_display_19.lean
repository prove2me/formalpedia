-- Prove2me | Theorems.Thm_MultiItemRev_MultiBuyer_display_19
-- name    : MultiItemRev.MultiBuyer.display_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:45.998156+00:00
-- url     : https://prove2.me/theorems/1cf11604-f9f2-43ac-9dcb-2f2bd5b40cfd
-- title:
--   (19), p. 49 — E[S(Y,Z) 1_{Y⁽¹⁾ ≥ Z⁽¹⁾}] ≤ 2 Rev^DS(Y) for independent goods and an NPT DS mechanism
-- statement:
--   Let $n \ge 1$, and let $Y, Z \in \mathbb R^n_+$ be the random vectors of the $n$ buyers' values for good 1 and good 2, with $Y$ and $Z$ independent (the buyers may be arbitrarily correlated within each good). Let $(q^j, s^j)_j$ be a feasible, IC-DS, IR-DS and NPT mechanism for the two goods with measurable payments and seller revenue $S = \sum_j s^j$. With $Y^{(1)} = \max_j Y^j$ and $Z^{(1)} = \max_j Z^j$,
--   $$\mathbb E\big[S(Y, Z)\,\mathbf 1_{Y^{(1)} \ge Z^{(1)}}\big] \le 2\,\mathrm{Rev}^{DS}(Y).$$
--
--   Together with the symmetric inequality (20) for the event $Z^{(1)} \ge Y^{(1)}$, this yields Theorem 33.
--
--   **Formalization Note** Since $S \ge 0$ under NPT, the expectation is the lower Lebesgue integral of $S$ over the event, in $[0,\infty]$. The law of $(Y,Z)$ is `twoGoodsN μY μZ`, the image of the product law.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 49, display (19), proof of Theorems 33 and 34

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.MultiBuyer

/-- Display (19), p. 49: for independent value vectors `Y` and `Z` of the two goods and an NPT,
IC-DS and IR-DS mechanism, `E[S(Y, Z) 1_{Y^{(1)} ≥ Z^{(1)}}] ≤ 2 Rev^{DS}(Y)`. -/
theorem display_19 {n : ℕ} (hn : 1 ≤ n) (μY μZ : Measure (Fin n → ℝ≥0))
    [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ] (M : MechanismN n (Fin 2))
    (hM : IsAdmissibleDS M) (hNPT : IsNPTN M) :
    ∫⁻ x in {x : Fin n → Fin 2 → ℝ≥0 | maxCoord (fun j => x j 1) ≤ maxCoord (fun j => x j 0)},
        ENNReal.ofReal (sellerRevenue M x) ∂(twoGoodsN μY μZ) ≤
      2 * RevDS (oneGoodN μY) := by sorry

end MultiItemRev.MultiBuyer
