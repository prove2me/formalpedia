-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_SeedProgram_rejection_s53
-- name    : OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:46:17.544738+00:00
-- url     : https://prove2.me/theorems/9622ffa5-8aab-457b-94a3-8145972dfab5
-- title:
--   OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection` of [lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.Compiler.SeedProgram`, with `open Amplifier ProjectionSeed CloudOrder`, `open scoped Classical`):
--
--   ```lean
--   lemma rejection_s53 (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
--       (a : GlobalRegularization.Node (CloudSpec.C t h)→Label) :
--       gap≤testRate ((CloudSpec.regularCSP t h).Bad a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Bit` and `OAI.MetricKMedian.PCP.testRate` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.Amplifier.capLoss`, `OAI.MetricKMedian.PCP.ExpanderFamily.Degree` and `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.Compiler.CSPRow`, `OAI.MetricKMedian.PCP.Compiler.CSPTable` and `OAI.MetricKMedian.PCP.Compiler.CSPTable.WellFormed` (definitions bundle `OAIQ053K010` of this split); `OAI.MetricKMedian.PCP.Amplifier.Label` (definitions bundle `OAIQ053K021` of this split); `OAI.MetricKMedian.PCP.PortCSP.Bad` (definitions bundle `OAIQ053K023` of this split); `OAI.MetricKMedian.PCP.BinaryCSP.rejection` and `OAI.MetricKMedian.PCP.Compiler.CSPTable.csp` (definitions bundle `OAIQ053K024` of this split); `OAI.MetricKMedian.PCP.Amplifier.nodeFintype`, `OAI.MetricKMedian.PCP.CloudCopies.RegularPort`, `OAI.MetricKMedian.PCP.FlexibleRegularization.graph`, `OAI.MetricKMedian.PCP.GlobalRegularization.Degree`, `OAI.MetricKMedian.PCP.GlobalRegularization.FastPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.Node`, `OAI.MetricKMedian.PCP.GlobalRegularization.StrongPort` and `OAI.MetricKMedian.PCP.Compiler.CloudOrder.cloudEmbed` (definitions bundle `OAIQ053K042` of this split); `OAI.MetricKMedian.PCP.ProjectionSeed.gap` (definitions bundle `OAIQ053K047` of this split); `OAI.MetricKMedian.PCP.Compiler.CloudSpec.C` (definitions bundle `OAIQ053K066` of this split); `OAI.MetricKMedian.PCP.Compiler.CloudSpec.EO` (definitions bundle `OAIQ053K067` of this split); `OAI.MetricKMedian.PCP.Compiler.CloudSpec.padding` and `OAI.MetricKMedian.PCP.Compiler.CloudSpec.regularCSP` (definitions bundle `OAIQ053K073` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean (declaration OAI.MetricKMedian.PCP.Compiler.SeedProgram.rejection)

import Mathlib
import Definitions.Def_OAIQ053K073

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedSound
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Amplifier ProjectionSeed CloudOrder
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
lemma rejection_s53 (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
    (a : GlobalRegularization.Node (CloudSpec.C t h)→Label) :
    gap≤testRate ((CloudSpec.regularCSP t h).Bad a) := by
  sorry
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
end
