-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_Compiler_CookProgram_projection_complete_s53
-- name    : OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:51:54.830492+00:00
-- url     : https://prove2.me/theorems/84a8ef3c-1df1-44eb-9e11-6018b31b57c5
-- title:
--   OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete` of [lean/OAI/Combinatorics/KMedian/PCP/UniformProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/PCP/UniformProjection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.Compiler.CookProgram`, with `open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier`, `open scoped Classical`):
--
--   ```lean
--   lemma projection_complete_s53 (n : ℕ) (x : Word)
--       (hx : ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) : (projection P p n x).Perfect
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Coverage.ProjectionInput.Perfect` (definitions bundle `OAIQ053K006` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.RightSize` (definitions bundle `OAIQ053K047` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.LeftSize` (definitions bundle `OAIQ053K053` of this split); `OAI.MetricKMedian.PCP.Compiler.SeedProgram.Width` (definitions bundle `OAIQ053K074` of this split); `OAI.MetricKMedian.PCP.Compiler.CookProgram.projection` (definitions bundle `OAIQ053K084` of this split); `OAI.MetricKMedian.Complexity.Word`, `OAI.MetricKMedian.Complexity.encodeBit` and `OAI.MetricKMedian.Complexity.encodePair` (the published bundle `Def_KMedianThreshold`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Coverage.projection_gap_np_reductions_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/PCP/UniformProjection.lean (declaration OAI.MetricKMedian.PCP.Compiler.CookProgram.projection_complete)

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K084

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPUniformProjection
namespace MetricKMedian.PCP.Compiler.CookProgram
open Binary Binary.Automatic CookLevin Complexity Tableau Amplifier
open scoped Classical

variable {verify : Word×Word→Bool}
variable (P : Turing.TM2ComputableInPolyTime Complexity.encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀k,Fintype (P.tm.Γ k)]
local instance instFintypeKTmBool_solutions_4_r5e6908_1 : Fintype P.tm.K := P.tm.kFin
local instance instFintypeΛTmBool_solutions_4_r5e6908_1 : Fintype P.tm.Λ := P.tm.ΛFin
local instance instFintypeσTmBool_solutions_4_r5e6908_1 : Fintype P.tm.σ := P.tm.σFin
noncomputable local instance instDecidableEqQueryKTmBoolΓΛσM_2_r5e6908_1 : DecidableEq (Query P.tm.m) := Classical.decEq _
attribute [local instance] OAI.MetricKMedian.PCP.Compiler.CookProgram.instNonemptyFinLengthCSPRowLabelSndListUnitAmplified
lemma projection_complete_s53 (n : ℕ) (x : Word)
    (hx : ∃ w : Word,w.length≤p.eval x.length ∧ verify (x,w)=true) : (projection P p n x).Perfect := by
  sorry
end MetricKMedian.PCP.Compiler.CookProgram

end Inline_PCPUniformProjection

end OAI
end
