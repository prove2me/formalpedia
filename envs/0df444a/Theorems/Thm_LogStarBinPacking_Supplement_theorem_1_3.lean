-- Prove2me | Theorems.Thm_LogStarBinPacking_Supplement_theorem_1_3
-- name    : LogStarBinPacking.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:17:13.106028+00:00
-- url     : https://prove2.me/theorems/561ed6b5-b4e3-4a97-b802-245a0479e07c
-- title:
--   Theorem 1.3 — an unconditional configuration-LP gap $\Omega(\log^*\mathrm{OPT})$ with three items near $1/3$
-- statement:
--   For a bin packing instance $J$ let $\mathrm{OPT}(J)$ be the least number of bins and $\mathrm{LP}(J)$ the value of the configuration LP (minimum total weight of feasible configurations, i.e. item sets of total size at most $1$, covering every item at least once). For $x\ge1$, $\log^*x$ is the number of base-two logarithms needed, applied iteratively, to reach a value at most one.
--
--   There is an absolute constant $\beta>0$ such that, for every fixed $\varepsilon>0$, there are arbitrarily large integers $M$ and instances $J$ of $3M$ items with all sizes in
--   $$
--   \Big(\tfrac13-\varepsilon,\tfrac13+\varepsilon\Big)\cap\Big(\tfrac14,\tfrac12\Big)
--   $$
--   satisfying
--   $$
--   \mathrm{OPT}(J)-\mathrm{LP}(J)\ \ge\ \beta\,\log^*\mathrm{OPT}(J).
--   $$
--
--   The additive integrality gap of the configuration LP is therefore unbounded, of order $\Omega(\log^*\mathrm{OPT})$, already for 3-partition instances with sizes arbitrarily close to $1/3$.
--
--   **Formalization Note** "Arbitrarily large $M$" means: for every $M_0$ there are $M\ge M_0$ and such an instance $J$. $\beta$ is chosen before $\varepsilon$. $\log^*$ is the published total iterated logarithm on $\mathbb R$, applied to $\mathrm{OPT}(J)$; sizes are rational and compared with the real $\varepsilon$ in $\mathbb R$.
--
--   Differences from the source:
--   - reading: "there are arbitrarily large integers M and instances J" → ∀ M₀, ∃ M ≥ M₀ and an instance J; reason: the standard reading of "arbitrarily large"
--   - encoding: log∗ x for x ≥ 1 → the published total logStar on ℝ applied to OPT(J); reason: the same values on x ≥ 1, and OPT(J) ≥ 1 whenever M ≥ 1
--   - encoding: rational sizes in an open interval with real ε → sizes cast to ℝ and compared with the real ε; reason: same instances
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Theorem 1.3, p.2 (proof §4.2, pp.17–18)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_PacketRouting_CongDil_Recurrences

namespace LogStarBinPacking.Supplement

open OAI.BinPackingGap

/-- **Theorem 1.3 (unconditional Ω(log∗ OPT) configuration-LP gap with three items per bin).**
Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript
(sha256 1d88425d…), Theorem 1.3, p.2.
There is an absolute constant `β > 0` such that, for every fixed `ε > 0`, there are arbitrarily
large integers `M` and instances `J` of `3M` items in `(1/3 − ε, 1/3 + ε) ∩ (1/4, 1/2)` satisfying
`OPT(J) − LP(J) ≥ β log∗ OPT(J)`.

**Formalization Note** "Arbitrarily large integers `M`" is read as: for every `M₀` there is such an
`M ≥ M₀` with an instance `J`. `β` is chosen before `ε`; `ε` is real and the rational sizes are
compared with it in `ℝ`. `J` is a published `Instance` (rational sizes in `(0, 1]`), `OPT` the
published `opt`, `LP` the published configuration LP `individualLP`, and `log∗` the published
`logStar` on `ℝ` (the least number of base-two logarithms bringing the argument to at most one),
applied to `OPT(J)`. -/
theorem theorem_1_3 :
    ∃ β : ℝ, 0 < β ∧ ∀ ε : ℝ, 0 < ε → ∀ M₀ : ℕ, ∃ M : ℕ, M₀ ≤ M ∧
      ∃ J : Instance, J.n = 3 * M ∧
        (∀ i : J.Item,
          1 / 3 - ε < ((J.size i : ℚ) : ℝ) ∧ ((J.size i : ℚ) : ℝ) < 1 / 3 + ε ∧
          1 / 4 < ((J.size i : ℚ) : ℝ) ∧ ((J.size i : ℚ) : ℝ) < 1 / 2) ∧
        β * (PacketRouting.CongDil.logStar (opt J : ℝ) : ℝ) ≤
          (opt J : ℝ) - individualLP J := by sorry

end LogStarBinPacking.Supplement
