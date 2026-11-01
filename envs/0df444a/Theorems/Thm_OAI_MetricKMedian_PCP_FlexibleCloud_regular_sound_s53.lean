-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_FlexibleCloud_regular_sound_s53
-- name    : OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:39:27.179387+00:00
-- url     : https://prove2.me/theorems/06f9e0a1-c94c-4318-957e-06f939d06377
-- title:
--   OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound` of [lean/OAI/Combinatorics/KMedian/Amplification/FlexibleCloud.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/FlexibleCloud.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.FlexibleCloud`, with `open Finset CloudCopies`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem regular_sound_s53 : C.rejection (decoded C a) ≤
--       6*(ExpanderFamily.growth:ℝ)*testRate ((regularCSP C embed).Bad a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.BinaryCSP` and `OAI.MetricKMedian.PCP.testRate` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.CloudCopies.Dart`, `OAI.MetricKMedian.PCP.ExpanderFamily.Degree`, `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort`, `OAI.MetricKMedian.PCP.ExpanderFamily.growth` and `OAI.MetricKMedian.PCP.ExpanderFamily.vertexFintype` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.CloudCopies.Active`, `OAI.MetricKMedian.PCP.CloudCopies.Copy`, `OAI.MetricKMedian.PCP.CloudCopies.Incident`, `OAI.MetricKMedian.PCP.CloudCopies.Node`, `OAI.MetricKMedian.PCP.CloudCopies.depth`, `OAI.MetricKMedian.PCP.CloudCopies.endpoint` and `OAI.MetricKMedian.PCP.PortCSP.Bad` (definitions bundle `OAIQ053K023` of this split); `OAI.MetricKMedian.PCP.BinaryCSP.rejection` (definitions bundle `OAIQ053K024` of this split); `OAI.MetricKMedian.PCP.CloudCopies.decoded` (definitions bundle `OAIQ053K035` of this split); `OAI.MetricKMedian.PCP.FlexibleCloud.RegularPort`, `OAI.MetricKMedian.PCP.FlexibleCloud.regularCSP` and `OAI.MetricKMedian.PCP.FlexibleCloud.regularGraph` (definitions bundle `OAIQ053K042` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53` and `OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/FlexibleCloud.lean (declaration OAI.MetricKMedian.PCP.FlexibleCloud.regular_sound)

import Mathlib
import Definitions.Def_OAIQ053K042

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleCloud

namespace MetricKMedian.PCP
open Finset CloudCopies
open scoped BigOperators Classical

namespace FlexibleCloud
variable {V E A : Type} [Fintype V] [Fintype E]
variable (C : BinaryCSP V E A)
variable (embed : ∀ v : Active C, Incident C v ↪ Copy C v)

variable [Fintype A] [DecidableEq A]

variable [Inhabited A] [Nonempty E] (a : Node C → A)

omit [Fintype V] in
theorem regular_sound_s53 : C.rejection (decoded C a) ≤
    6*(ExpanderFamily.growth:ℝ)*testRate ((regularCSP C embed).Bad a) := by
  sorry

end FlexibleCloud
end MetricKMedian.PCP

end Inline_PCPFlexibleCloud

end OAI
end
