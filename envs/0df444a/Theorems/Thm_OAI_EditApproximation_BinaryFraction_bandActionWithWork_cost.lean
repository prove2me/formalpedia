-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_bandActionWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.bandActionWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:25:40.65078+00:00
-- url     : https://prove2.me/theorems/68ea3dee-1163-4314-950a-fb7965126dca
-- title:
--   OAI.EditApproximation.BinaryFraction.bandActionWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.bandActionWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBandAction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBandAction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem bandActionWithWork_cost {M ny : ℕ} (b : ℕ)
--       (initial : Fin M → TargetInterval ny → BinaryFraction)
--       (table : ℕ → Fin M × TargetInterval ny → BinaryFraction)
--       (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval ny))
--       (G K t Be Bk Bi Bt E : ℕ) (hband : band ≠ []) (hb : 0 < b) (hM : 0 < M)
--       (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
--       (hi : ∀ action ∈ band, ∀ j, (initial j (action j)).width ≤ Bi)
--       (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
--         (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
--       (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
--       (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
--         0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
--           (table s ((listedBandCoordinateVector band).get i)).value ≤
--             (initial ((listedBandCoordinateVector band).get i).1
--               ((listedBandCoordinateVector band).get i).2).value) :
--       (bandActionWithWork b initial table eta kappa band G K t).2 ≤
--         bandActionBitBudget M (listedBandCoordinates band).length b band.length G K t Be Bk Bi Bt E
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.listedBandCoordinateVector`, `OAI.EditApproximation.BinaryFraction.bandActionBitBudget` and `OAI.EditApproximation.BinaryFraction.bandActionWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.listedBandCoordinates` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.instDecidableEqTargetInterval` (the published bundle `Def_EditApproxScheme_08`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBandAction.lean (declaration OAI.EditApproximation.BinaryFraction.bandActionWithWork_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem bandActionWithWork_cost {M ny : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval ny → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval ny → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval ny))
    (G K t Be Bk Bi Bt E : ℕ) (hband : band ≠ []) (hb : 0 < b) (hM : 0 < M)
    (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hi : ∀ action ∈ band, ∀ j, (initial j (action j)).width ≤ Bi)
    (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
        (table s ((listedBandCoordinateVector band).get i)).value ≤
          (initial ((listedBandCoordinateVector band).get i).1
            ((listedBandCoordinateVector band).get i).2).value) :
    (bandActionWithWork b initial table eta kappa band G K t).2 ≤
      bandActionBitBudget M (listedBandCoordinates band).length b band.length G K t Be Bk Bi Bt E := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
