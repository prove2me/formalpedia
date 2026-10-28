-- Prove2me | Theorems.Thm_OAI_UniqueGamesTheorem_Inverse_KMSFourthMoment_rankComponent_fourth_moment_le_of_hybrid
-- name    : OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:46:43.028925+00:00
-- url     : https://prove2.me/theorems/860285e8-104a-4f98-9033-4c0ff36c8be4
-- title:
--   OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid: intermediate lemma from OpenAI, The Unique Games Theorem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.UniqueGamesTheorem.theorem11`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Unique Games Theorem*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` of [lean/OAI/Computability/UniqueGames/Inverse/KMSBasisComparisonPseudorandomTupleMapLemmas.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Inverse/KMSBasisComparisonPseudorandomTupleMapLemmas.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment`, with `open scoped BigOperators Classical`, `open UniqueGamesTheorem.Integration.BinaryLinear (F2)`, `open UniqueGamesTheorem.Inverse.KMSAnalytic`, `open UniqueGamesTheorem.Appendix`, `open UniqueGamesTheorem.Fourier.MatrixRestrictions`):
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
--   **Definitions.** The statement is written with `OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridDerivative`, `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.Parameter`, `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.order` and `OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype` (definitions bundle `OAIQ086U000` of this split); `OAI.UniqueGamesTheorem.Inverse.KMSAnalytic.rankComponent` (definitions bundle `OAIQ086U009` of this split); `OAI.UniqueGamesTheorem.Integration.BinaryLinear.F2` (the published bundle `Def_UniqueGamesTheorem`).
--
--   **Used by.** The proof of `OAI.UniqueGamesTheorem.Inverse.ShortcodeTheorem.inversePrinciple` of this split imports it.
-- source:
--   OpenAI, The Unique Games Theorem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Unique-Games-Theorem-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/UniqueGames/Inverse/KMSBasisComparisonPseudorandomTupleMapLemmas.lean (declaration OAI.UniqueGamesTheorem.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid)

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_UniqueGamesTheorem
import Definitions.Def_OAIQ086U009

section

attribute [-instance] _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.kernelFintype _root_.OAI.UniqueGamesTheorem.Clean.AdviceImageLaw.rangeFintype _root_.OAI.UniqueGamesTheorem.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.UniqueGamesTheorem.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.UniqueGamesTheorem.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.UniqueGamesTheorem.Gadget.OrientationVectors.nonzeroAction _root_.OAI.UniqueGamesTheorem.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.UniqueGamesTheorem.Quadratic.binaryFieldFintype _root_.OAI.UniqueGamesTheorem.Quadratic.blockOrientationFintype _root_.OAI.UniqueGamesTheorem.Quadratic.fieldLineFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.dualFintype _root_.OAI.UniqueGamesTheorem.Reduction.ActualGame.mapFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.UniqueGamesTheorem.Soundness.ConditionalIncidences.zeroBits _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.partnerModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.UniqueGamesTheorem.Soundness.PartnerLinear.sourceModule _root_.OAI.UniqueGamesTheorem.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.UniqueGamesTheorem.Soundness.RawMapLaw.rawMapsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Inverse.KMSAnalytic
open UniqueGamesTheorem.Appendix
open UniqueGamesTheorem.Fourier.MatrixRestrictions

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
end UniqueGamesTheorem.Inverse.KMSFourthMoment

end

end OAI
end
