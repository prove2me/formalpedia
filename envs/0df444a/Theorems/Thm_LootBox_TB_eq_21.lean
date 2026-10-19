-- Prove2me | Theorems.Thm_LootBox_TB_eq_21
-- name    : LootBox.TB.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:47.455088+00:00
-- url     : https://prove2.me/theorems/9807b5cf-efe9-4f2d-bf85-83f8dc33ccb9
-- title:
--   Eq. (21), p. 33 — at price µ/e the traditional box earns at least (µ/e)·log(1/(1/e + (1+σ²/µ²)/N))
-- statement:
--   Let $F$ be a valuation law (non-negative, finite variance) with mean $\mu > 0$ and variance $\sigma^2$, and let $N \ge 1$. At the price $p = \mu/e$ the normalized revenue of the traditional box satisfies
--
--   $$R_{TB}(\mu/e) \;\ge\; \frac{\mu}{e}\,\log\!\left( \frac{1}{\frac1e + \frac{1+\sigma^2/\mu^2}{N}} \right).$$
--
--   Since $R_{TB} \ge R_{TB}(\mu/e)$, this gives the lower bound of Theorem 3 at an explicit price, and its right-hand side tends to $\mu/e$ as $N \to \infty$.
--
--   **Formalization Note** The right-hand side is mapped into $[0,\infty]$ by $x \mapsto \max(x,0)$ (`ENNReal.ofReal`). It is negative only for small $N$ (for instance $N = 1$), where the inequality is then the trivial $R_{TB}(\mu/e) \ge 0$; this loses nothing, since revenue is non-negative.
-- source:
--   Chen, Elmachtoub, Hamilton & Lei, Loot Box Pricing and Design, manuscript submitted August 2019 (Management Science doi:10.1287/mnsc.2020.3748), proof of Theorem 3, Eq. (21), p. 33

import Mathlib
import Definitions.Def_LootBox_TB_Setting

namespace LootBox.TB

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_21 (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (hμ : 0 < mean F)
    (N : ℕ) [NeZero N] :
    ENNReal.ofReal (mean F / Real.exp 1 *
        Real.log (1 / (1 / Real.exp 1 + (1 + var F / mean F ^ 2) / N))) ≤
      revenue F N (mean F / Real.exp 1) := by sorry

end LootBox.TB
