-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Inverse_KMSFourthMoment_rankComponent_fourth_moment_le_of_hybrid
-- name    : OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:47:21.605004+00:00
-- url     : https://prove2.me/theorems/4991c205-28ae-463d-9ac7-7402b350ecac
-- title:
--   OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid` of [lean/OAI/Computability/MaxCut/Games/A5Induction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/A5Induction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Inverse.KMSFourthMoment`, with `open scoped BigOperators Classical`, `open MaxCutGames.Integration.BinaryLinear (F2)`, `open MaxCutGames.Inverse.KMSAnalytic`, `open MaxCutGames.Appendix`, `open MaxCutGames.Fourier.MatrixRestrictions`):
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
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Appendix.Derivatives.hybridDerivative`, `OAI.MaxCutGames.Fourier.MatrixRestrictions.Parameter`, `OAI.MaxCutGames.Fourier.MatrixRestrictions.order`, `OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype` and `OAI.MaxCutGames.Integration.BinaryLinear.F2` (definitions bundle `OAIQ087A000` of this split); `OAI.MaxCutGames.Inverse.KMSAnalytic.rankComponent` (definitions bundle `OAIQ087A012` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/A5Induction.lean (declaration OAI.MaxCutGames.Inverse.KMSFourthMoment.rankComponent_fourth_moment_le_of_hybrid)

import Mathlib
import Definitions.Def_OAIQ087A012

section

attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSAffineRestrictionSplit.freeFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Integration.BinaryLinear (F2)
open MaxCutGames.Inverse.KMSAnalytic
open MaxCutGames.Appendix
open MaxCutGames.Fourier.MatrixRestrictions

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
end MaxCutGames.Inverse.KMSFourthMoment

end OAI
end
