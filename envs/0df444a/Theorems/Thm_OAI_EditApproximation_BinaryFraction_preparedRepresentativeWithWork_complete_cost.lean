-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedRepresentativeWithWork_complete_cost
-- name    : OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:18.507732+00:00
-- url     : https://prove2.me/theorems/9805588b-ad5b-43cc-bcbd-5a96dad4e876
-- title:
--   OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost` of [lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedRepresentativeWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedRepresentativeWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem preparedRepresentativeWithWork_complete_cost {nx ny M : ℕ}
--       (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
--       (hPpos : 0 < P) (tau theta : BinaryFraction)
--       (child : Fin M → TargetInterval ny → BinaryFraction)
--       (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
--       (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B)
--       (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
--       (hchild : ∀ i q, (child i q).width ≤ B) :
--       (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau theta child).2 ≤
--         wideMaterializationBitBudget M P B +
--         representativeCompleteBitBudget M (wideActionGridWithWork M parent center b P).1.length (4 * B + 20) +
--         (wideActionGridWithWork M parent center b P).1.length + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork`, `OAI.EditApproximation.BinaryFraction.representativeCompleteBitBudget` and `OAI.EditApproximation.BinaryFraction.wideMaterializationBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.wideActionGridWithWork` (the published bundle `Def_EditApproxScheme_06`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.BinaryFraction.preparedLocalOnlineActionsWithWork_cost`, `OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_uniform_cost`, `OAI.EditApproximation.queryLocalRandomSources_work_bound` and `OAI.EditApproximation.queryOnlineSourceGather_work_bound` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Binary/BinaryPreparedRepresentativeWork.lean (declaration OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_complete_cost)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem preparedRepresentativeWithWork_complete_cost {nx ny M : ℕ}
    (parent : TargetInterval nx) (center : TargetInterval ny) (b P B : ℕ)
    (hPpos : 0 < P) (tau theta : BinaryFraction)
    (child : Fin M → TargetInterval ny → BinaryFraction)
    (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b ≤ B) (hP : Nat.size P ≤ B)
    (htau : tau.width ≤ B) (htheta : theta.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B) :
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau theta child).2 ≤
      wideMaterializationBitBudget M P B +
      representativeCompleteBitBudget M (wideActionGridWithWork M parent center b P).1.length (4 * B + 20) +
      (wideActionGridWithWork M parent center b P).1.length + 1 := by
  sorry

end BinaryFraction
end EditApproximation

end OAI
end
