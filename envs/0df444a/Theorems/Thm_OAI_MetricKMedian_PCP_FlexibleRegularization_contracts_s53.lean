-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_FlexibleRegularization_contracts_s53
-- name    : OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:39:21.533599+00:00
-- url     : https://prove2.me/theorems/6560cb27-2fe0-4711-a648-0342665416d3
-- title:
--   OAI.MetricKMedian.PCP.FlexibleRegularization.contracts_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.FlexibleRegularization.contracts` of [lean/OAI/Combinatorics/KMedian/Amplification/FlexibleRegularization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/FlexibleRegularization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.FlexibleRegularization`, with `open Finset`, `open scoped BigOperators Classical`, `open GlobalRegularization`):
--
--   ```lean
--   theorem contracts_s53 : (graph C cloudEmbed padEmbed).Contracts (1/2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.BinaryCSP` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.ExpanderFamily.Degree`, `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort` and `OAI.MetricKMedian.PCP.ExpanderFamily.vertexFintype` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.CloudCopies.Active`, `OAI.MetricKMedian.PCP.CloudCopies.Copy`, `OAI.MetricKMedian.PCP.CloudCopies.Incident` and `OAI.MetricKMedian.PCP.CloudCopies.Node` (definitions bundle `OAIQ053K023` of this split); `OAI.MetricKMedian.PCP.PortGraph.Contracts` (definitions bundle `OAIQ053K026` of this split); `OAI.MetricKMedian.PCP.CloudCopies.RegularPort`, `OAI.MetricKMedian.PCP.FlexibleRegularization.graph`, `OAI.MetricKMedian.PCP.GlobalRegularization.Degree`, `OAI.MetricKMedian.PCP.GlobalRegularization.FastPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.Node`, `OAI.MetricKMedian.PCP.GlobalRegularization.StrongPort` and `OAI.MetricKMedian.PCP.GlobalRegularization.depth` (definitions bundle `OAIQ053K042` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53` and `OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/FlexibleRegularization.lean (declaration OAI.MetricKMedian.PCP.FlexibleRegularization.contracts)

import Mathlib
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K042

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleRegularization

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace FlexibleRegularization
variable {V E A : Type} [Fintype V] [Fintype E] [Nonempty E]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (C : BinaryCSP V E A)

open GlobalRegularization

variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ Node C)

omit [Fintype V] [Nonempty E] [Fintype A] [DecidableEq A] [Inhabited A] in
theorem contracts_s53 : (graph C cloudEmbed padEmbed).Contracts (1/2) := by
  sorry

end FlexibleRegularization
end MetricKMedian.PCP

end Inline_PCPFlexibleRegularization

end OAI
end
