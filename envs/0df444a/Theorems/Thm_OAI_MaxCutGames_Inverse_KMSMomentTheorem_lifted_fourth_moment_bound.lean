-- Prove2me | Theorems.Thm_OAI_MaxCutGames_Inverse_KMSMomentTheorem_lifted_fourth_moment_bound
-- name    : OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T17:46:28.340378+00:00
-- url     : https://prove2.me/theorems/56f1f706-38f5-4609-8485-f10ed9eb16e9
-- title:
--   OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound: intermediate lemma from OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound` of [lean/OAI/Computability/MaxCut/Games/KMSMomentTheorem.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/KMSMomentTheorem.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaxCutGames.Inverse.KMSMomentTheorem`, with `open scoped BigOperators Classical`, `open KMS KMSBasisComparison KMSBasisComparisonPseudorandom`, `open KMSAnalytic KMSFourthMoment KMSMomentConstants`):
--
--   ```lean
--   theorem lifted_fourth_moment_bound
--       (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
--       (ell : ℕ) (hell : r ≤ ell) (n : ℕ)
--       (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * r) ε)
--       (i : ℕ) (hi : i ≤ r) :
--       (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
--         fourthMomentConstant r *
--           (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaxCutGames.Inverse.KMS.Ambient`, `OAI.MaxCutGames.Inverse.KMS.F2`, `OAI.MaxCutGames.Inverse.KMS.Vertex`, `OAI.MaxCutGames.Inverse.KMSBasisComparison.BasisMap`, `OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype`, `OAI.MaxCutGames.Inverse.KMSBasisComparison.liftedIndicator`, `OAI.MaxCutGames.Inverse.KMSBasisComparisonPseudorandom.TuplePseudorandom` and `OAI.MaxCutGames.Inverse.KMSMomentConstants.fourthMomentConstant` (definitions bundle `OAIQ087A005` of this split); `OAI.MaxCutGames.Inverse.KMSAnalytic.rankComponent` (definitions bundle `OAIQ087A012` of this split).
--
--   **Used by.** The proof of `OAI.MaxCutGames.Inverse.ShortcodeTheorem.inversePrinciple` of this split imports it.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/MaxCut/Games/KMSMomentTheorem.lean (declaration OAI.MaxCutGames.Inverse.KMSMomentTheorem.lifted_fourth_moment_bound)

import Mathlib
import Definitions.Def_OAIQ087A012

section

attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Gadget.StageQuotient.spaceFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisAutomorphismFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Quadratic.finiteBlockOrientation _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Inverse.KMSMomentTheorem
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open KMSAnalytic KMSFourthMoment KMSMomentConstants

theorem lifted_fourth_moment_bound
    (r : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (ell : ℕ) (hell : r ≤ ell) (n : ℕ)
    (S : Finset (Vertex n ell)) (hS : TuplePseudorandom S (2 * r) ε)
    (i : ℕ) (hi : i ≤ r) :
    (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 4) ≤
      fourthMomentConstant r *
        (𝔼 X : BasisMap n ell, rankComponent i (liftedIndicator S) X ^ 2) * ε := by
  sorry

end
end MaxCutGames.Inverse.KMSMomentTheorem

end OAI
end
