-- Prove2me | Theorems.Thm_LL_S72PerronWindow_leaf_log_sum
-- name    : LL_S72PerronWindow.leaf_log_sum
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T13:16:09.837914+00:00
-- url     : https://prove2.me/theorems/3c3822c5-c568-43d1-b450-a0f20b2e5c1b
-- title:
--   The summed Perron remainder over $J$ is $O(Y^{1/200})$
-- statement:
--   For every $\varepsilon>0$ there are $K\ge0$ and $C$ such that for all real $x\ge C$ and all real $w$ with $Y/2\le w\le 6Y$, where $Y=x^{11/20+\varepsilon}$, $$\sum_{m\in J}\frac{(w/m)^{1/2}}{1+Y\,|\log(w/m)|}\le K\,Y^{1/200}.$$
-- source:
--   Baker, Harman and Pintz 1997, proof of Lemma 29, pages 43 and 44, after Titchmarsh Lemma 3.19.

import Mathlib
import Definitions.Def_LL_S72PerronWindow_rightInterval

open Classical Complex
open scoped BigOperators
open MeasureTheory

namespace LL_S72PerronWindow
theorem leaf_log_sum {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ w : ℝ, x ^ (11 / 20 + ε) / 2 ≤ w →
      w ≤ 6 * x ^ (11 / 20 + ε) →
        ∑ m ∈ rightInterval ε x, (w / m) ^ (1 / 2 : ℝ) /
            (1 + x ^ (11 / 20 + ε) * |Real.log (w / m)|) ≤
          K * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by sorry
end LL_S72PerronWindow
