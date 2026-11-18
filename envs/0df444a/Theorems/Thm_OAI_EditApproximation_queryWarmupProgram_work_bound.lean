-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryWarmupProgram_work_bound
-- name    : OAI.EditApproximation.queryWarmupProgram_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:45.852207+00:00
-- url     : https://prove2.me/theorems/fd65cdfb-6a98-4884-be28-1c33128dbb81
-- title:
--   OAI.EditApproximation.queryWarmupProgram_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryWarmupProgram_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryWarmupProgramCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryWarmupProgramCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryWarmupProgram_work_bound {ι : Type*} {nx ny M : ℕ}
--       (parent : TargetInterval nx) (N P F B C : ℕ) (hP : 0 < P) (a : BinaryFraction)
--       (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
--       (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
--       (q : TargetInterval ny) (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
--       (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
--       (hPb : Nat.size P ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
--       (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
--       (hi : ∀ r, ((initialRead r).value oracle).width ≤ B)
--       (hc : ∀ r, ((childRead r).value oracle).width ≤ B)
--       (hiC : ∀ r, (initialRead r).work oracle readWork ≤ C)
--       (hcC : ∀ r, (childRead r).work oracle readWork ≤ C) :
--       (queryWarmupProgram parent N P F a initialRead childRead q).work oracle readWork ≤
--         queryWarmupProgramBitBudget M P F B C
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryWarmupProgramBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.BitQuery` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.TargetInterval`, `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.queryWarmupProgram` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryWarmupProgramCost.lean (declaration OAI.EditApproximation.queryWarmupProgram_work_bound)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open BinaryFraction

theorem queryWarmupProgram_work_bound {ι : Type*} {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F B C : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
    (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction)
    (q : TargetInterval ny) (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 10 ≤ B) (hN : Nat.size N ≤ B) (hF : Nat.size F + 2 ≤ B) (hFpos : 1 ≤ F)
    (hPb : Nat.size P ≤ B) (hnx : Nat.size nx + 2 ≤ B) (hny : Nat.size ny + 2 ≤ B)
    (hM : Nat.size M ≤ B) (ha : a.width ≤ B)
    (hi : ∀ r, ((initialRead r).value oracle).width ≤ B)
    (hc : ∀ r, ((childRead r).value oracle).width ≤ B)
    (hiC : ∀ r, (initialRead r).work oracle readWork ≤ C)
    (hcC : ∀ r, (childRead r).work oracle readWork ≤ C) :
    (queryWarmupProgram parent N P F a initialRead childRead q).work oracle readWork ≤
      queryWarmupProgramBitBudget M P F B C := by
  sorry

end EditApproximation

end OAI
end
