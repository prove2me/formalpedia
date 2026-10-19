-- Prove2me | Theorems.Thm_LootBox_TB_eq_17
-- name    : LootBox.TB.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:49.067367+00:00
-- url     : https://prove2.me/theorems/872fa4d8-c116-4941-8d87-8aac8ee4187c
-- title:
--   Eq. (17), p. 33 — t/µ ≤ E[r(t)] ≤ t/µ + 1 + σ²/µ² for the first passage of an i.i.d. non-negative walk
-- statement:
--   Let $F$ be a valuation law (non-negative, finite variance) with mean $\mu > 0$ and variance $\sigma^2$. Let $w_0, w_1, \dots$ be i.i.d. with law $F$, and for a level $t \ge 0$ let $r(t) = \inf\{ j \ge 1 : t \le w_0 + \dots + w_{j-1} \}$. Then
--
--   $$\frac{t}{\mu} \;\le\; \mathbb E[r(t)] \;\le\; \frac{t}{\mu} + 1 + \frac{\sigma^2}{\mu^2}.$$
--
--   In the proof of Theorem 3 the level is $t = Np_N$. The bound controls the expected index at which the backward walk of collected valuations first exceeds the threshold, and feeds the lower bound (21) through Jensen's inequality.
--
--   **Formalization Note** The statement is posed for every level $t \ge 0$; the page uses $t = Np_N$. The expectation is a lower Lebesgue integral in $[0,\infty]$, so an infinite expectation would violate the upper bound rather than vanish. The page justifies the upper bound by an inspection-paradox identity that holds only asymptotically; the inequality itself is true (the overshoot bound of Lorden, 1970), and only the inequality is posed.
-- source:
--   Chen, Elmachtoub, Hamilton & Lei, Loot Box Pricing and Design, manuscript submitted August 2019 (Management Science doi:10.1287/mnsc.2020.3748), proof of Theorem 3, Eq. (17), p. 33

import Mathlib
import Definitions.Def_LootBox_TB_Setting

namespace LootBox.TB

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_17 (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (hμ : 0 < mean F)
    (t : ℝ) (ht : 0 ≤ t) :
    ENNReal.ofReal (t / mean F) ≤ ∫⁻ w, ((firstPassage w t : ℕ∞) : ℝ≥0∞) ∂(walkLaw F) ∧
      ∫⁻ w, ((firstPassage w t : ℕ∞) : ℝ≥0∞) ∂(walkLaw F) ≤
        ENNReal.ofReal (t / mean F + 1 + var F / mean F ^ 2) := by sorry

end LootBox.TB
