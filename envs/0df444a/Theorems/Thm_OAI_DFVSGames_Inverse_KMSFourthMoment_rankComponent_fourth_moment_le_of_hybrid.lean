-- Prove2me | Theorems.Thm_OAI_DFVSGames_Inverse_KMSFourthMoment_rankComponent_fourth_moment_le_of_hybrid
-- name    : OAI.DFVSGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:04:51.208934+00:00
-- url     : https://prove2.me/theorems/144e5031-684f-4cbf-9a0e-602072de0348
-- title:
--   OAI.DFVSGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid: intermediate lemma from OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DFVSGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` of [lean/OAI/Computability/DirectedFeedback/Probability/KMSMomentConstants.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Probability/KMSMomentConstants.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DFVSGames.Inverse.KMSFourthMoment`, with `open scoped BigOperators Classical`, `open DFVSGames.Integration.BinaryLinear (F2)`, `open DFVSGames.Inverse.KMSAnalytic`, `open DFVSGames.Appendix`, `open DFVSGames.Fourier.MatrixRestrictions`):
--
--   ```lean
--   theorem rankComponent_fourth_moment_le_of_hybrid (i : ℕ)
--       (f : (E →ₗ[F2] F) → ℝ) (H : ℝ) (hH0 : 0 ≤ H)
--       (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
--         order A B ≤ i →
--         (𝔼 N, Derivatives.hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ H) :
--       (𝔼 X, rankComponent i f X ^ 4) ≤
--         (2 : ℝ) ^ (103 * i * i) * H * (𝔼 X, rankComponent i f X ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DFVSGames.Fourier.MatrixRestrictions.Parameter` and `OAI.DFVSGames.Integration.BinaryLinear.F2` (definitions bundle `OAIQ085D000` of this split); `OAI.DFVSGames.Appendix.Derivatives.hybridDerivative`, `OAI.DFVSGames.Fourier.MatrixRestrictions.order` and `OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype` (definitions bundle `OAIQ085D007` of this split); `OAI.DFVSGames.Inverse.KMSAnalytic.rankComponent` (definitions bundle `OAIQ085D027` of this split).
--
--   **Used by.** The proofs of `OAI_DFVSGames_Inverse_KMSExpansion_kms_expansion` and `OAI.DFVSGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound` of this split import it.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DirectedFeedback/Probability/KMSMomentConstants.lean (declaration OAI.DFVSGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid)

import Mathlib
import Definitions.Def_OAIQ085D027

section

attribute [-instance] _root_.OAI.DFVSGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open DFVSGames.Integration.BinaryLinear (F2)
open DFVSGames.Inverse.KMSAnalytic
open DFVSGames.Appendix
open DFVSGames.Fourier.MatrixRestrictions

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

theorem rankComponent_fourth_moment_le_of_hybrid (i : ℕ)
    (f : (E →ₗ[F2] F) → ℝ) (H : ℝ) (hH0 : 0 ≤ H)
    (hH : ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
      order A B ≤ i →
      (𝔼 N, Derivatives.hybridDerivative A B T (rankComponent i f) N ^ 2) ≤ H) :
    (𝔼 X, rankComponent i f X ^ 4) ≤
      (2 : ℝ) ^ (103 * i * i) * H * (𝔼 X, rankComponent i f X ^ 2) := by
  sorry

end
end DFVSGames.Inverse.KMSFourthMoment

end OAI
end
