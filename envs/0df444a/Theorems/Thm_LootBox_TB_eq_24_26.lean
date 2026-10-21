-- Prove2me | Theorems.Thm_LootBox_TB_eq_24_26
-- name    : LootBox.TB.eq_24_26
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:04.413977+00:00
-- url     : https://prove2.me/theorems/a3c1a4e6-6448-4d6e-bf03-8191696ee87a
-- title:
--   Eqs. (24)–(26), p. 34 (corrected) — R_TB ≤ µe^{ζ_N−1}/(1−ϵ) + µ/((1−ϵ)N) + (1−ϵ)σ²(1+log N)/(ϵ²µN)
-- statement:
--   Let $F$ be a valuation law (non-negative, finite variance) with mean $\mu > 0$ and variance $\sigma^2$, let $N \ge 1$ and $0 < \epsilon < 1$, and let $\zeta_N = \sum_{i=1}^N \frac1i - \log N - \gamma$. Then the optimal normalized revenue of the traditional box satisfies
--
--   $$R_{TB} \;\le\; \frac{\mu\, e^{\zeta_N - 1}}{1-\epsilon} \;+\; \frac{\mu}{(1-\epsilon)N} \;+\; \frac{(1-\epsilon)\,\sigma^2\,(1+\log N)}{\epsilon^2\,\mu\,N}.$$
--
--   With $\epsilon = N^{-1/3}$ the right-hand side tends to $\mu/e$, because $\zeta_N \to 0$; this is the upper half of the limit in Theorem 3.
--
--   **Formalization Note** This is a corrected form of the page's bounds (24)–(26). The printed per-price bound (25) inherits the index slip of (16) (the term $1/r_N$ is dropped) and is false: for $V \equiv 1$, $N = 1000$ and $p = 1/N$ the revenue is $H_N/N \approx 0.007485$, while (25) gives $\approx 0.007014$. The printed maximization over $p_N$ also ignores prices $p > \mu/(1-\epsilon)$, where the bound $p\,\zeta_N$ of (25) is unbounded. The constants above come from the page's argument with both gaps repaired: the extra $\frac{\mu}{(1-\epsilon)N}$ accounts for the term $1/r_N$, $1 + \log N$ bounds $H_N$, and the first term is the maximum over $p$ of $p(\log\frac{\mu}{(1-\epsilon)p} + \zeta_N)$. The printed (26) is not posed: no proof of it is available.
-- source:
--   Chen, Elmachtoub, Hamilton & Lei, Loot Box Pricing and Design, manuscript submitted August 2019 (Management Science doi:10.1287/mnsc.2020.3748), proof of Theorem 3, Eqs. (24)–(26), p. 34, corrected (see note)

import Mathlib
import Definitions.Def_LootBox_TB_Setting

namespace LootBox.TB

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem eq_24_26 (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ValLaw F) (hμ : 0 < mean F)
    (N : ℕ) [NeZero N] (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    optRevenue F N ≤
      ENNReal.ofReal (mean F * Real.exp (zeta N - 1) / (1 - ε) + mean F / ((1 - ε) * N) +
        (1 - ε) * var F * (1 + Real.log N) / (ε ^ 2 * mean F * N)) := by sorry

end LootBox.TB
