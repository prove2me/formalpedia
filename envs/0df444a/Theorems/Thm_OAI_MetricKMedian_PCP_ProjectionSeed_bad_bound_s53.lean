-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_ProjectionSeed_bad_bound_s53
-- name    : OAI.MetricKMedian.PCP.ProjectionSeed.bad_bound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:45:04.044458+00:00
-- url     : https://prove2.me/theorems/9f3d59e6-1458-43e4-91e7-a850ad81adb9
-- title:
--   OAI.MetricKMedian.PCP.ProjectionSeed.bad_bound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.ProjectionSeed.bad_bound` of [lean/OAI/Combinatorics/KMedian/Projection/Seed.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/Seed.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.ProjectionSeed`, with `open Finset`, `open scoped Classical BigOperators`, `open Amplifier`):
--
--   ```lean
--   lemma bad_bound_s53 : bad.CollisionBound contraction
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Bit` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.BiProjection.CollisionBound`, `OAI.MetricKMedian.PCP.ExpanderFamily.Degree` and `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.Amplifier.Label` (definitions bundle `OAIQ053K021` of this split); `OAI.MetricKMedian.PCP.CloudCopies.RegularPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.FastPort` and `OAI.MetricKMedian.PCP.GlobalRegularization.StrongPort` (definitions bundle `OAIQ053K042` of this split); `OAI.MetricKMedian.PCP.ProjectionSeed.LeftLabel` (definitions bundle `OAIQ053K046` of this split); `OAI.MetricKMedian.PCP.ProjectionSeed.Degree`, `OAI.MetricKMedian.PCP.ProjectionSeed.LeftPort`, `OAI.MetricKMedian.PCP.ProjectionSeed.Port`, `OAI.MetricKMedian.PCP.ProjectionSeed.RightLabel` and `OAI.MetricKMedian.PCP.ProjectionSeed.contraction` (definitions bundle `OAIQ053K047` of this split); `OAI.MetricKMedian.PCP.ProjectionSeed.bad` (definitions bundle `OAIQ053K053` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/Seed.lean (declaration OAI.MetricKMedian.PCP.ProjectionSeed.bad_bound)

import Mathlib
import Definitions.Def_OAIQ053K053

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionSeed

namespace MetricKMedian.PCP
open Finset
open scoped Classical BigOperators

namespace ProjectionSeed
open Amplifier

lemma bad_bound_s53 : bad.CollisionBound contraction := by
  sorry
end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
end
