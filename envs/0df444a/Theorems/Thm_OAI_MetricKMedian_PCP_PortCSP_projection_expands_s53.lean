-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_PortCSP_projection_expands_s53
-- name    : OAI.MetricKMedian.PCP.PortCSP.projection_expands_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:39:41.433996+00:00
-- url     : https://prove2.me/theorems/8fb2d348-809c-4e03-8424-2d507a2eac2a
-- title:
--   OAI.MetricKMedian.PCP.PortCSP.projection_expands_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.PortCSP.projection_expands` of [lean/OAI/Combinatorics/KMedian/Projection/CSPProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/CSPProjection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.PortCSP`, with `open Finset`, `open scoped BigOperators Classical`):
--
--   ```lean
--   lemma projection_expands_s53 (hG : G.Contracts (1/2)) : (C.projection chosen).Expands (1/4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.PortGraph` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.PortCSP` (definitions bundle `OAIQ053K023` of this split); `OAI.MetricKMedian.PCP.BiProjection.Expands` (definitions bundle `OAIQ053K024` of this split); `OAI.MetricKMedian.PCP.PortGraph.Contracts` (definitions bundle `OAIQ053K026` of this split); `OAI.MetricKMedian.PCP.PortCSP.projection` (definitions bundle `OAIQ053K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/CSPProjection.lean (declaration OAI.MetricKMedian.PCP.PortCSP.projection_expands)

import Mathlib
import Definitions.Def_OAIQ053K043

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCSPProjection

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D} [DecidableEq A]
variable (C : PortCSP G A)
variable (chosen : V × D → A × A) (hchosen : ∀ p, C.Legal p (chosen p))
omit [DecidableEq A]

variable [Fintype V] [Fintype D] [Fintype A] [Nonempty V] [Nonempty D] [Nonempty A]
omit [Fintype A] [Nonempty A]

lemma projection_expands_s53 (hG : G.Contracts (1/2)) : (C.projection chosen).Expands (1/4) := by
  sorry
end PortCSP
end MetricKMedian.PCP

end Inline_PCPCSPProjection

end OAI
end
