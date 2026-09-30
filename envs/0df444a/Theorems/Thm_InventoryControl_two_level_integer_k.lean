-- Prove2me | Theorems.Thm_InventoryControl_two_level_integer_k
-- name    : InventoryControl.two_level_integer_k
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:11:00.866366+00:00
-- url     : https://prove2.me/theorems/f8efe01c-41a3-4c41-aef9-d9a1082d6b74
-- title:
--   Sect. 9.2.1, p. 177: the integer ratio is chosen by $k^*/k' \le (k'+1)/k^*$, and $A_1/e_1 \ge A_2/e_2$ gives $k = 1$
-- statement:
--   In the two-level serial system with $d, A_1, A_2, e_1, e_2 > 0$ and
--   $k^{*} = \sqrt{A_2e_1/(A_1e_2)}$, the comparison between two consecutive positive integer
--   ratios is settled by the same geometric-mean rule as the integer EOQ of Sect. 4.1.2: for every
--   integer $k' \ge 1$,
--
--   $$ C(k') \le C(k'+1) \quad\Longleftrightarrow\quad \frac{k^{*}}{k'} \le \frac{k'+1}{k^{*}}, $$
--
--   and if $A_1/e_1 \ge A_2/e_2$, that is $k^{*} \le 1$, then $k = 1$ is optimal among all
--   positive integers.
--
--   The first statement is what the book means by "it is optimal to choose $k = k'$ if
--   $k^{*}/k' \le (k'+1)/k^{*}$, otherwise $k = k'+1$", since $C(k)$ is unimodal in $k$. The second
--   says that when the ratio of ordering to holding cost is larger downstream, the two items
--   should share one batch: no stock of item 2 is ever held and the two-stage system collapses to
--   a single stage, a conclusion the book notes also holds for time-varying demand (Axsäter and
--   Nuttle, 1987).
-- source:
--   Sven Axsäter, Inventory Control, 3rd ed., Springer 2015, DOI 10.1007/978-3-319-15729-0, p. 177, Sect. 9.2.1, the paragraph after Eq. (9.13): 'It is optimal to choose k = k' if k*/k' <= (k' + 1)/k*. Otherwise k = k' + 1 is optimal. If A1/e1 >= A2/e2 we get k = 1'

import Definitions.Def_InventoryControl_serial

namespace InventoryControl

theorem two_level_integer_k (d A1 A2 e1 e2 : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) :
    (∀ k : ℕ, 0 < k →
        (twoLevelOptCost d A1 A2 e1 e2 k ≤ twoLevelOptCost d A1 A2 e1 e2 (k + 1)
          ↔ Real.sqrt (A2 * e1 / (A1 * e2)) / k ≤ (k + 1) / Real.sqrt (A2 * e1 / (A1 * e2))))
      ∧ (A2 / e2 ≤ A1 / e1 → ∀ k : ℕ, 0 < k →
          twoLevelOptCost d A1 A2 e1 e2 1 ≤ twoLevelOptCost d A1 A2 e1 e2 k) := by sorry

end InventoryControl
