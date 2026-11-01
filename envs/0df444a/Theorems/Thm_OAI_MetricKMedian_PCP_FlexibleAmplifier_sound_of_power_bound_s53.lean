-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_FlexibleAmplifier_sound_of_power_bound_s53
-- name    : OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:44:50.327045+00:00
-- url     : https://prove2.me/theorems/887d8884-f8e8-4ba6-9646-cb878ecc3636
-- title:
--   OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound` of [lean/OAI/Combinatorics/KMedian/Amplification/FlexibleBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/FlexibleBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.FlexibleAmplifier`, with `open Amplifier`, `open scoped Classical`):
--
--   ```lean
--   theorem sound_of_power_bound_s53 (a : Node C → Advice Degree Label radius) (r : ℝ)
--       (hb : (powered C cloudEmbed padEmbed).rejection a /384 ≤ r) :
--       min (2*C.rejection (FlexibleRegularization.decoded C padEmbed ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps))) (1/(capLoss:ℝ)) ≤ r
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Advice`, `OAI.MetricKMedian.PCP.BinaryCSP` and `OAI.MetricKMedian.PCP.Bit` (definitions bundle `OAIQ053K008` of this split); `OAI.MetricKMedian.PCP.Amplifier.capLoss`, `OAI.MetricKMedian.PCP.Amplifier.radius`, `OAI.MetricKMedian.PCP.Amplifier.steps`, `OAI.MetricKMedian.PCP.ExpanderFamily.Degree` and `OAI.MetricKMedian.PCP.ExpanderFamily.SmallPort` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.Amplifier.Label` (definitions bundle `OAIQ053K021` of this split); `OAI.MetricKMedian.PCP.CloudCopies.Active`, `OAI.MetricKMedian.PCP.CloudCopies.Copy`, `OAI.MetricKMedian.PCP.CloudCopies.Incident` and `OAI.MetricKMedian.PCP.CloudCopies.Node` (definitions bundle `OAIQ053K023` of this split); `OAI.MetricKMedian.PCP.BinaryCSP.rejection` (definitions bundle `OAIQ053K024` of this split); `OAI.MetricKMedian.PCP.PortGraph.plurality` (definitions bundle `OAIQ053K036` of this split); `OAI.MetricKMedian.PCP.Amplifier.Degree`, `OAI.MetricKMedian.PCP.CloudCopies.RegularPort`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.Edge`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.Node`, `OAI.MetricKMedian.PCP.FlexibleRegularization.graph`, `OAI.MetricKMedian.PCP.GlobalRegularization.Degree`, `OAI.MetricKMedian.PCP.GlobalRegularization.FastPort`, `OAI.MetricKMedian.PCP.GlobalRegularization.Node` and `OAI.MetricKMedian.PCP.GlobalRegularization.StrongPort` (definitions bundle `OAIQ053K042` of this split); `OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype`, `OAI.MetricKMedian.PCP.FlexibleAmplifier.powered` and `OAI.MetricKMedian.PCP.FlexibleRegularization.decoded` (definitions bundle `OAIQ053K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Amplification/FlexibleBound.lean (declaration OAI.MetricKMedian.PCP.FlexibleAmplifier.sound_of_power_bound)

import Mathlib
import Definitions.Def_OAIQ053K036
import Definitions.Def_OAIQ053K047

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.InitialAlphabet.edgeNonempty _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFlexibleBound
namespace MetricKMedian.PCP.FlexibleAmplifier
open Amplifier
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
variable (C : BinaryCSP V E Label)
variable (cloudEmbed : ∀ v : CloudCopies.Active C, CloudCopies.Incident C v ↪ CloudCopies.Copy C v)
variable (padEmbed : CloudCopies.Node C ↪ GlobalRegularization.Node C)
omit [Fintype V] in
theorem sound_of_power_bound_s53 (a : Node C → Advice Degree Label radius) (r : ℝ)
    (hb : (powered C cloudEmbed padEmbed).rejection a /384 ≤ r) :
    min (2*C.rejection (FlexibleRegularization.decoded C padEmbed ((FlexibleRegularization.graph C cloudEmbed padEmbed).plurality a steps steps))) (1/(capLoss:ℝ)) ≤ r := by
  sorry

end MetricKMedian.PCP.FlexibleAmplifier

end Inline_PCPFlexibleBound

end OAI
end
