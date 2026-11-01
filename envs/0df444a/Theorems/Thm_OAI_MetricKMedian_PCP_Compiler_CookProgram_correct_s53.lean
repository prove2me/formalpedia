-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_CookProgram_correct_s53
-- name    : OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:47:57.483992+00:00
-- url     : https://prove2.me/theorems/1787debf-9a4c-4e71-ac76-f099baf27410
-- title:
--   OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.Compiler.CookProgram.correct` of [lean/OAI/Combinatorics/KMedian/CookLevin/CookTable.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookTable.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.Compiler.CookProgram`, with `open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory`, `open scoped Classical`):
--
--   ```lean
--   lemma correct_s53 (x : Word) : (∃ a, ((table P p x).csp (wellFormed P p x)).Satisfies a) ↔
--       ∃ w : Word, w.length≤p.eval x.length ∧ verify (x,w)=true
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Compiler.CSPRow`, `OAI.MetricKMedian.PCP.Tableau.Query` and `OAI.MetricKMedian.PCP.Tableau.Value` (definitions bundle `OAIQ053K010` of this split); `OAI.MetricKMedian.PCP.Compiler.LocalCompiler.Label` (definitions bundle `OAIQ053K011` of this split); `OAI.MetricKMedian.PCP.BinaryCSP.Satisfies` and `OAI.MetricKMedian.PCP.Compiler.CSPTable.csp` (definitions bundle `OAIQ053K024` of this split); `OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_2` (definitions bundle `OAIQ053K077` of this split); `OAI.MetricKMedian.PCP.Compiler.CookProgram.table` and `OAI.MetricKMedian.PCP.Compiler.CookProgram.wellFormed` (definitions bundle `OAIQ053K082` of this split); `OAI.MetricKMedian.Complexity.Word`, `OAI.MetricKMedian.Complexity.encodeBit` and `OAI.MetricKMedian.Complexity.encodePair` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.Compiler.CookProgram.initial_correct_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookTable.lean (declaration OAI.MetricKMedian.PCP.Compiler.CookProgram.correct)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K082

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.PortCSP.powerEdge_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookTable
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau TableauDirectory
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeKTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeΛTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instFintypeσTmBool_solutions_2
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedValueKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instInhabitedQueryKTmBoolΓΛσM
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instDecidableEqQueryKTmBoolΓΛσM
lemma correct_s53 (x : Word) : (∃ a, ((table P p x).csp (wellFormed P p x)).Satisfies a) ↔
    ∃ w : Word, w.length≤p.eval x.length ∧ verify (x,w)=true := by
  sorry
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPCookTable

end OAI
end
