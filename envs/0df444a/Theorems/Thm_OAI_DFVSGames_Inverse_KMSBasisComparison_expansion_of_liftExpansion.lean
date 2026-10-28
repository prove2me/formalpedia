-- Prove2me | Theorems.Thm_OAI_DFVSGames_Inverse_KMSBasisComparison_expansion_of_liftExpansion
-- name    : OAI.DFVSGames.Inverse.KMSBasisComparison.expansion_of_liftExpansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:59:48.341494+00:00
-- url     : https://prove2.me/theorems/c7745267-7e68-4d07-a5e0-f6fca2e235d2
-- title:
--   OAI.DFVSGames.Inverse.KMSBasisComparison.expansion_of_liftExpansion: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Inverse.KMSBasisComparison.expansion_of_liftExpansion` of [lean/OAI/Computability/DirectedFeedback/Games/KMSBasisComparisonRetention.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/KMSBasisComparisonRetention.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Inverse.KMSBasisComparison`, with `open scoped Classical`, `open KMSBasisComparisonPseudorandom`):
--
--   ```lean
--   theorem expansion_of_liftExpansion (h : LiftExpansionPrinciple) :
--       KMS.ExpansionPrinciple
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Inverse.KMS.ExpansionPrinciple` (definitions bundle `OAIQ085D003` of this split); `OAI.DFVSGames.Inverse.KMSBasisComparison.LiftExpansionPrinciple` (definitions bundle `OAIQ085D027` of this split).
--
--   **Used by.** The proof of `OAI.DFVSGames.theorem11` of this split imports it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Games/KMSBasisComparisonRetention.lean (declaration OAI.DFVSGames.Inverse.KMSBasisComparison.expansion_of_liftExpansion)

import Mathlib
import Definitions.Def_OAIQ085D027

section

attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical
open KMSBasisComparisonPseudorandom

theorem expansion_of_liftExpansion (h : LiftExpansionPrinciple) :
    KMS.ExpansionPrinciple := by
  sorry

end
end DFVSGames.Inverse.KMSBasisComparison

end OAI
end
