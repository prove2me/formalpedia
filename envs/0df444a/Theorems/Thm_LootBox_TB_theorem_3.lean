-- Prove2me | Theorems.Thm_LootBox_TB_theorem_3
-- name    : LootBox.TB.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:04.395121+00:00
-- url     : https://prove2.me/theorems/8e1f472a-0816-42b1-8b8c-040af3b51588
-- title:
--   Theorem 3, p. 13 — the optimal normalized traditional-box revenue R_TB converges to µ/e as N → ∞
-- statement:
--   A monopolist sells $N$ virtual items through traditional loot boxes: each box, sold at a fixed price $p$, contains an item drawn uniformly at random from the $N$ items, duplicates included. A customer's valuations $V_1,\dots,V_N$ are i.i.d. with a law $F$ on $[0,\infty)$ of mean $\mu$ and finite variance $\sigma^2$; a duplicate is worth nothing. The customer is myopic: they buy the next box if and only if its expected utility $\frac1N\sum_{i \notin S_t} V_i - p$ is non-negative, where $S_t$ is the set of items already owned, and they leave forever otherwise. Let $R_{TB}(p) = p\,\mathbb E[\#\text{ purchases}]/N$ and $R_{TB} = \sup_{p>0} R_{TB}(p)$, both depending on $N$. Then
--
--   $$\lim_{N \to \infty} R_{TB} = \frac{\mu}{e}.$$
--
--   So a seller using traditional loot boxes obtains, in the limit of a large catalog, a fraction $1/e$ of the mean valuation per item, whatever the valuation distribution; by contrast unique boxes (Theorem 2) and the grand bundle obtain the full mean $\mu$.
--
--   **Formalization Note** The sequence is indexed by $n \mapsto R_{TB}$ at $N = n+1$, so that the law of the uniform draws is defined; this does not affect the limit. Revenue is valued in $[0,\infty]$ and the limit is $\max(\mu/e, 0) = \mu/e$. No hypothesis $\mu > 0$ is needed: if $\mu = 0$ the valuations vanish almost surely, nothing is bought, and both sides are $0$. Theorem 3 also states two finite-$N$ bounds; the lower one is posed, at the explicit price $\mu/e$, as the milestone Eq. (21), and the printed upper one, whose proof on p. 34 is broken, is replaced by the corrected milestone Eqs. (24)–(26).
-- source:
--   Chen, Elmachtoub, Hamilton & Lei, Loot Box Pricing and Design, manuscript submitted August 2019 (Management Science doi:10.1287/mnsc.2020.3748), Theorem 3, p. 13 (the limit clause "Moreover, lim_{N→∞} R_TB = µ/e"); model §2, §2.1, pp. 6–11

import Mathlib
import Definitions.Def_LootBox_TB_Setting

namespace LootBox.TB

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem theorem_3 (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) :
    Tendsto (fun n : ℕ => optRevenue F (n + 1)) atTop
      (𝓝 (ENNReal.ofReal (mean F / Real.exp 1))) := by sorry

end LootBox.TB
