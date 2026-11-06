-- Prove2me | Theorems.Thm_LogStarBinPacking_theorem_1_1
-- name    : LogStarBinPacking.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:45.365965+00:00
-- url     : https://prove2.me/theorems/96987fb4-af17-44e8-84b8-07b3dd5ddf15
-- title:
--   Theorem 1.1 — NP-hardness of an additive $\Omega(\log^*\mathrm{OPT})$ gap with three items per bin
-- statement:
--   There is an absolute constant $\alpha>0$ such that, for every fixed $\varepsilon>0$, the following promise problem is NP-hard. An input is a bin packing instance $J$ of $3M$ items for an integer $M\ge1$, with sizes in
--   $$
--   \Big(\frac13-\varepsilon,\frac13+\varepsilon\Big)\cap\Big(\frac14,\frac12\Big).
--   $$
--   The two cases are
--
--   1. $\mathrm{OPT}(J)=M$;
--   2. $\mathrm{OPT}(J)>M+\alpha\log^*M$.
--
--   So bin packing is NP-hard to approximate within an additive $o(\log^*\mathrm{OPT})$ even when every bin holds at most three items.
--
--   **Formalization Note** NP-hardness means that every language in NP has a `ThreeItemGapReduction α ε`: a polynomial-time finite-alphabet map to valid inputs, into case 1 on members and case 2 on non-members. $\alpha$ is chosen before $\varepsilon$, and $\varepsilon$ is real.
--
--   Differences from the source:
--   - reading: "the promise problem is NP-hard" → every CookLevin.InNP language has a ThreeItemGapReduction α ε; reason: the standard Karp reading of a promise problem's NP-hardness, as in the published PackingGapNPHard
--   - encoding: log∗ x for x ≥ 1 → the published total logStar on ℝ applied to M ≥ 1; reason: the same values on x ≥ 1
--   - encoding: an instance J of 3M items with rational sizes → the pair (M, J) with J a valid raw list of sizes p/q, compared with the real ε in ℝ; reason: the encoded form of the same inputs
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_PacketRouting_CongDil_Recurrences
import Definitions.Def_LogStarBinPacking_ThreeItemGapReduction

namespace LogStarBinPacking

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Theorem 1.1.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Theorem 1.1, p.2.
There is an absolute constant `α > 0` such that, for every fixed `ε > 0`, the following promise
problem is NP-hard. An input is a bin packing instance `J` of `3M` items for an integer
`M ≥ 1`, with sizes in `(1/3 − ε, 1/3 + ε) ∩ (1/4, 1/2)`. The two cases are (i) `OPT(J) = M`;
(ii) `OPT(J) > M + α log∗ M`.

**Formalization Note** NP-hardness of the promise problem: every language in NP
(`CookLevin.InNP`) has a `ThreeItemGapReduction α ε`, a polynomial-time finite-alphabet map to
valid inputs that lands in case (i) on members and in case (ii) on non-members; this is the reading
of the published `PackingGapNPHard`. `α` is chosen before `ε`; `ε` is real. -/
theorem theorem_1_1 :
    ∃ α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ∀ L : BitLanguage, CookLevin.InNP L →
      Nonempty (ThreeItemGapReduction α ε L) := by sorry

end LogStarBinPacking
