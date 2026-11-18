-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedBandActionWithWork_cost
-- name    : OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:26:11.116781+00:00
-- url     : https://prove2.me/theorems/e8c6a5fc-3d99-465e-a133-5cc70a2c7329
-- title:
--   OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBandAction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBandAction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem preparedBandActionWithWork_cost {M : ℕ} {σ : Type*} [DecidableEq σ]
--       (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
--       (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G K t Be Bk Bm Bt E : ℕ)
--       (hband : band ≠ []) (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
--       (hm : ∀ j, (mass.get j).width ≤ Bm) (hmpos : ∀ j, 0 < (mass.get j).value)
--       (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
--         (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
--       (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
--       (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
--         0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
--           (table s ((listedBandCoordinateVector band).get i)).value ≤
--             (mass.get ((listedBandCoordinateVector band).get i).1).value) :
--       (preparedBandActionWithWork mass table eta kappa band G K t).2 ≤
--         preparedBandActionBitBudget M (listedBandCoordinates band).length band.length G K t Be Bk Bm Bt E
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.listedBandCoordinateVector`, `OAI.EditApproximation.BinaryFraction.preparedBandActionBitBudget` and `OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.listedBandCoordinates` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.bandActionWithWork_cost` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryBandAction.lean (declaration OAI.EditApproximation.BinaryFraction.preparedBandActionWithWork_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem preparedBandActionWithWork_cost {M : ℕ} {σ : Type*} [DecidableEq σ]
    (mass : Vector BinaryFraction M) (table : ℕ → Fin M × σ → BinaryFraction)
    (eta kappa : BinaryFraction) (band : List (Fin M → σ)) (G K t Be Bk Bm Bt E : ℕ)
    (hband : band ≠ []) (he : eta.width ≤ Be) (hk : kappa.width ≤ Bk)
    (hm : ∀ j, (mass.get j).width ≤ Bm) (hmpos : ∀ j, 0 < (mass.get j).value)
    (ht : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (table s ((listedBandCoordinateVector band).get i)).width ≤ Bt)
    (heabs : |eta.value| ≤ E) (hkrange : 0 ≤ kappa.value ∧ kappa.value ≤ 1)
    (htrange : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      0 ≤ (table s ((listedBandCoordinateVector band).get i)).value ∧
        (table s ((listedBandCoordinateVector band).get i)).value ≤
          (mass.get ((listedBandCoordinateVector band).get i).1).value) :
    (preparedBandActionWithWork mass table eta kappa band G K t).2 ≤
      preparedBandActionBitBudget M (listedBandCoordinates band).length band.length G K t Be Bk Bm Bt E := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
