-- Prove2me | Theorems.Thm_OAI_DFVSGames_Decoder_MatrixGap_parameters_of_inverse
-- name    : OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:28:57.151834+00:00
-- url     : https://prove2.me/theorems/24a9faa8-df9c-4a3b-b873-13f858f233ec
-- title:
--   OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse` of [lean/OAI/Computability/DirectedFeedback/Games/StageData.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/StageData.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Decoder.MatrixGap`, with `open Integration.BinaryLinear Reduction ActualSource Foundations.Games`, `open Integration`):
--
--   ```lean
--   theorem parameters_of_inverse (hinverse : Inverse.Shortcode.InversePrinciple)
--       (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Decoder.MatrixGap.Parameters` (definitions bundle `OAIQ085D007` of this split); `OAI.DFVSGames.Inverse.Shortcode.InversePrinciple` (definitions bundle `OAIQ085D009` of this split).
--
--   **Used by.** The proof of `OAI.DFVSGames.theorem11` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/StageData.lean (declaration OAI.DFVSGames.Decoder.MatrixGap.parameters_of_inverse)

import Mathlib
import Definitions.Def_OAIQ085D007
import Definitions.Def_OAIQ085D009

section

attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.MatrixGap

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open Integration

noncomputable section

theorem parameters_of_inverse (hinverse : Inverse.Shortcode.InversePrinciple)
    (p : ℚ) (hp : 0 < p) : Nonempty (Parameters p) := by
  sorry

end
end DFVSGames.Decoder.MatrixGap

end OAI
end
