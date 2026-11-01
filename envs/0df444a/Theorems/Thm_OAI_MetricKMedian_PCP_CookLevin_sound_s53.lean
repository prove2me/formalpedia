-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_CookLevin_sound_s53
-- name    : OAI.MetricKMedian.PCP.CookLevin.sound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:50:40.282768+00:00
-- url     : https://prove2.me/theorems/cf118612-fc26-4413-836f-36347d2230b7
-- title:
--   OAI.MetricKMedian.PCP.CookLevin.sound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.CookLevin.sound` of [lean/OAI/Combinatorics/KMedian/CookLevin/CookLevin.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookLevin.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.CookLevin`, with `open Turing Turing.TM2 Function Finset`, `open Complexity Tableau`, `open scoped Classical`):
--
--   ```lean
--   lemma sound_s53 (x : Word) (ha : ∃ a, (system P p x).Satisfies a) :
--       ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x,w)=true
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.Tableau.Query` and `OAI.MetricKMedian.PCP.Tableau.Value` (definitions bundle `OAIQ053K010` of this split); `OAI.MetricKMedian.PCP.FiniteCSP.Satisfies`, `OAI.MetricKMedian.PCP.Tableau.BoundaryClause`, `OAI.MetricKMedian.PCP.Tableau.Clause` and `OAI.MetricKMedian.PCP.Tableau.Var` (definitions bundle `OAIQ053K011` of this split); `OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions` (definitions bundle `OAIQ053K077` of this split); `OAI.MetricKMedian.PCP.CookLevin.space`, `OAI.MetricKMedian.PCP.CookLevin.system` and `OAI.MetricKMedian.PCP.CookLevin.time` (definitions bundle `OAIQ053K082` of this split); `OAI.MetricKMedian.Complexity.Word`, `OAI.MetricKMedian.Complexity.encodeBit` and `OAI.MetricKMedian.Complexity.encodePair` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.Compiler.CookProgram.correct_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/CookLevin/CookLevin.lean (declaration OAI.MetricKMedian.PCP.CookLevin.sound)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K082

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.inputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.outputSymbolInhabited _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.symbolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeCoding _root_.OAI.MetricKMedian.PCP.Compiler.CookProgram.tapeHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.CookLevin.testNonempty _root_.OAI.MetricKMedian.PCP.CookLevin.valueInhabited _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.edgeFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPCookLevin

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]

attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeKTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeΛTmBool_solutions
attribute [local instance] OAI.MetricKMedian.PCP.CookLevin.instFintypeσTmBool_solutions
lemma sound_s53 (x : Word) (ha : ∃ a, (system P p x).Satisfies a) :
    ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x,w)=true := by
  sorry
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
end
