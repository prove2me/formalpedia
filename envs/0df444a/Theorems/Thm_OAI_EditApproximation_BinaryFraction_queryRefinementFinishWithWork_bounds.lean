-- Prove2me | Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryRefinementFinishWithWork_bounds
-- name    : OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:30.050963+00:00
-- url     : https://prove2.me/theorems/0015b108-7801-41c1-a422-9b972ef7a3f4
-- title:
--   OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork_bounds: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork_bounds` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryFinishCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryFinishCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation.BinaryFraction`):
--
--   ```lean
--   theorem queryRefinementFinishWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
--       (N P F B R G O : ℕ) (a delta : BinaryFraction)
--       (initial : TargetInterval ny → BinaryFraction × ℕ) (t : ℕ)
--       (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction)
--       (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
--       (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction)
--       (q : TargetInterval ny) (hB : 10 ≤ B) (hP : 0 < P) (hFpos : 1 ≤ F)
--       (hN : Nat.size N ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
--       (hM : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
--       (ha : a.width ≤ B) (hd : delta.width ≤ B)
--       (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
--       (he : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).1.width ≤ B)
--       (heR : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2 ≤ R)
--       (hc : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).1.width ≤ B)
--       (hcR : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).2 ≤ R)
--       (hgroups : ∀ action ∈ groups, action.connection.width ≤ connectionWordBudget M (B + 4))
--       (honline : ∀ action ∈ online, action.connection.width ≤ connectionWordBudget M (B + 4))
--       (hglen : groups.length ≤ G) (holen : online.length ≤ O) :
--       (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online
--         currentKeys currentWords q).1.width ≤ preparedKernelWordBudget M B ∧
--       (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online
--         currentKeys currentWords q).2 ≤ queryRefinementFinishBitBudget M P F B R G O
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.connectionWordBudget`, `OAI.EditApproximation.BinaryFraction.preparedKernelWordBudget` and `OAI.EditApproximation.BinaryFraction.queryRefinementFinishBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryBellmanAction` and `OAI.EditApproximation.BinaryFraction` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.BinaryFraction.queryChildReadWithWork` and `OAI.EditApproximation.BinaryFraction.queryHistoryReadWithWork` (the published bundle `Def_EditApproxScheme_07`); `OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.BinaryFraction.queryLocalRefinement_finish_bounds` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryFinishCost.lean (declaration OAI.EditApproximation.BinaryFraction.queryRefinementFinishWithWork_bounds)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryRefinementFinishWithWork_bounds {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F B R G O : ℕ) (a delta : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (t : ℕ)
    (earlierKeys : List (Fin M × ℕ × TargetInterval ny)) (earlierWords : List BinaryFraction)
    (groups online : List (BinaryBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
    (currentKeys : List (Fin M × TargetInterval ny)) (currentWords : List BinaryFraction)
    (q : TargetInterval ny) (hB : 10 ≤ B) (hP : 0 < P) (hFpos : 1 ≤ F)
    (hN : Nat.size N ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hPb : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (hd : delta.width ≤ B)
    (hi : ∀ r, (initial r).1.width ≤ B) (hR : ∀ r, (initial r).2 ≤ R)
    (he : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).1.width ≤ B)
    (heR : ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).2 ≤ R)
    (hc : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).1.width ≤ B)
    (hcR : ∀ i r, (queryChildReadWithWork currentKeys currentWords i r).2 ≤ R)
    (hgroups : ∀ action ∈ groups, action.connection.width ≤ connectionWordBudget M (B + 4))
    (honline : ∀ action ∈ online, action.connection.width ≤ connectionWordBudget M (B + 4))
    (hglen : groups.length ≤ G) (holen : online.length ≤ O) :
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online
      currentKeys currentWords q).1.width ≤ preparedKernelWordBudget M B ∧
    (queryRefinementFinishWithWork parent N P F a delta initial t earlierKeys earlierWords groups online
      currentKeys currentWords q).2 ≤ queryRefinementFinishBitBudget M P F B R G O := by
  sorry

end EditApproximation.BinaryFraction

end OAI
end
