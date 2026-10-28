-- Prove2me | Theorems.Thm_OAI_DFVSGames_theorem11
-- name    : OAI.DFVSGames.theorem11
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:34:43.670012+00:00
-- url     : https://prove2.me/theorems/3f5d5302-0c9d-4562-99f4-000024789823
-- title:
--   OAI.DFVSGames.theorem11: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.theorem11` of [lean/OAI/Computability/DirectedFeedback/RankGraph/OutputDef.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/OutputDef.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames`):
--
--   ```lean
--   theorem theorem11 (ε δ : ℝ)
--       (hε : 0 < ε) (hεhalf : ε < 1 / 2)
--       (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
--       Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Explicit.MachineOutputContract.BinaryGapReduction` (definitions bundle `OAIQ085D013` of this split).
--
--   **Used by.** The proof of `OAI.DirectedFeedback.main` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/RankGraph/OutputDef.lean (declaration OAI.DFVSGames.theorem11)

import Mathlib
import Definitions.Def_OAIQ085D013

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames

theorem theorem11 (ε δ : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) := by
  sorry

end DFVSGames

end OAI
end
