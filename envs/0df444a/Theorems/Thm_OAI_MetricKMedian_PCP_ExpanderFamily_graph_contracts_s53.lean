-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_ExpanderFamily_graph_contracts_s53
-- name    : OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:35:53.974589+00:00
-- url     : https://prove2.me/theorems/f1878c58-0d9b-4e7c-918d-a7efce99d6bc
-- title:
--   OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts` of [lean/OAI/Combinatorics/KMedian/Expanders/ExpanderFamily.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Expanders/ExpanderFamily.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.ExpanderFamily`, with `open Finset`, `open scoped BigOperators`):
--
--   ```lean
--   lemma graph_contracts_s53 : ∀ n, (graph n).Contracts (1/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.ExpanderFamily.Degree`, `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort`, `OAI.MetricKMedian.PCP.ExpanderFamily.Vertex` and `OAI.MetricKMedian.PCP.ExpanderFamily.vertexFintype` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.ExpanderFamily.graph` (definitions bundle `OAIQ053K023` of this split); `OAI.MetricKMedian.PCP.PortGraph.Contracts` (definitions bundle `OAIQ053K026` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53` and `OAI.MetricKMedian.PCP.GlobalRegularization.strong_contracts_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Expanders/ExpanderFamily.lean (declaration OAI.MetricKMedian.PCP.ExpanderFamily.graph_contracts)

import Mathlib
import Definitions.Def_OAIQ053K023
import Definitions.Def_OAIQ053K026

section

attribute [-instance] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPExpanderFamily

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace ExpanderFamily

lemma graph_contracts_s53 : ∀ n, (graph n).Contracts (1/2) := by
  sorry

end ExpanderFamily
end MetricKMedian.PCP

end Inline_PCPExpanderFamily

end OAI
end
