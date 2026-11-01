-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_SeedProgram_good_bound_s53
-- name    : OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:48:06.673228+00:00
-- url     : https://prove2.me/theorems/f7ddf84f-0bce-478e-9be5-d3f47f8654bf
-- title:
--   OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound` of [lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.Compiler.SeedProgram`, with `open Amplifier ProjectionSeed CloudOrder`, `open scoped Classical`):
--
--   ```lean
--   lemma good_bound_s53 (hl : allLegal t=true) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a) :
--       (good t h).CollisionBound contraction
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Bit` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.Amplifier.capLoss`, `OAI.MetricKMedian.PCP.BiProjection.CollisionBound`, `OAI.MetricKMedian.PCP.ExpanderFamily.Degree` and `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.Compiler.CSPRow`, `OAI.MetricKMedian.PCP.Compiler.CSPTable` and `OAI.MetricKMedian.PCP.Compiler.CSPTable.WellFormed` (definitions bundle `OAIQ053K010` of this split); `OAI.MetricKMedian.PCP.Amplifier.Label` (definitions bundle `OAIQ053K021` of this split); `OAI.MetricKMedian.PCP.BinaryCSP.rejection` and `OAI.MetricKMedian.PCP.Compiler.CSPTable.csp` (definitions bundle `OAIQ053K024` of this split); `OAI.MetricKMedian.PCP.Amplifier.nodeFintype`, `OAI.MetricKMedian.PCP.CloudCopies.RegularPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.Degree`, `OAI.MetricKMedian.PCP.GlobalRegularization.FastPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.Node` and `OAI.MetricKMedian.PCP.GlobalRegularization.StrongPort` (definitions bundle `OAIQ053K042` of this split); `OAI.MetricKMedian.PCP.ProjectionSeed.contraction` (definitions bundle `OAIQ053K047` of this split); `OAI.MetricKMedian.PCP.Compiler.CloudSpec.C` (definitions bundle `OAIQ053K066` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.allLegal` (definitions bundle `OAIQ053K074` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good` (definitions bundle `OAIQ053K081` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/SeedSound.lean (declaration OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound)

import Mathlib
import Definitions.Def_OAIQ053K081

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
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
lemma good_bound_s53 (hl : allLegal t=true) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a) :
    (good t h).CollisionBound contraction := by
  sorry
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
end
