-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_SeedProgram_output_sound_s53
-- name    : OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:51:25.263476+00:00
-- url     : https://prove2.me/theorems/9f0d2ad7-99e1-4c02-85f5-3aa96a9a16ef
-- title:
--   OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound` of [lean/OAI/Combinatorics/KMedian/CookLevin/SeedInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/SeedInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.Compiler.SeedProgram`, with `open Binary Binary.Automatic Amplifier ProjectionTable`, `open scoped Classical`):
--
--   ```lean
--   lemma output_sound_s53 (n : ℕ) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
--       (ε : ℝ) (hε : 0≤ε) (hn : ProjectionSeed.contraction^n≤ε^2) : (output t h n).Sound ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Coverage.ProjectionInput.Sound` (definitions bundle `OAIQ053K006` of this split); `OAI.MetricKMedian.PCP.Amplifier.capLoss` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.Compiler.CSPRow`, `OAI.MetricKMedian.PCP.Compiler.CSPTable` and `OAI.MetricKMedian.PCP.Compiler.CSPTable.WellFormed` (definitions bundle `OAIQ053K010` of this split); `OAI.MetricKMedian.PCP.Amplifier.Label` (definitions bundle `OAIQ053K021` of this split); `OAI.MetricKMedian.PCP.BinaryCSP.rejection` and `OAI.MetricKMedian.PCP.Compiler.CSPTable.csp` (definitions bundle `OAIQ053K024` of this split); `OAI.MetricKMedian.PCP.ProjectionSeed.contraction` and `OAI.MetricKMedian.PCP.Compiler.SeedProgram.RightSize` (definitions bundle `OAIQ053K047` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.LeftSize` (definitions bundle `OAIQ053K053` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.Width` (definitions bundle `OAIQ053K074` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.output` (definitions bundle `OAIQ053K083` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/SeedInput.lean (declaration OAI.MetricKMedian.PCP.Compiler.SeedProgram.output_sound)

import Mathlib
import Definitions.Def_OAIQ053K083

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPSeedInput
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
lemma output_sound_s53 (n : ℕ) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
    (ε : ℝ) (hε : 0≤ε) (hn : ProjectionSeed.contraction^n≤ε^2) : (output t h n).Sound ε := by
  sorry
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

end OAI
end
