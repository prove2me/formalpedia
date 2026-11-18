-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryInitialConeProgramAt_work_bound
-- name    : OAI.EditApproximation.queryInitialConeProgramAt_work_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:31.346685+00:00
-- url     : https://prove2.me/theorems/0be77498-2266-4108-84fa-cd60597532a7
-- title:
--   OAI.EditApproximation.queryInitialConeProgramAt_work_bound: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryInitialConeProgramAt_work_bound` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryInitialProgramCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryInitialProgramCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open BinaryFraction`):
--
--   ```lean
--   theorem queryInitialConeProgramAt_work_bound {ι : Type*} {n : ℕ}
--       (sourceLength N P F Amax B C : ℕ) (hP : 0 < P) (A a : BinaryFraction)
--       (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
--       (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
--       (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B) (hF : Nat.size F ≤ B)
--       (hnx : Nat.size sourceLength ≤ B) (hny : Nat.size n ≤ B)
--       (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
--       (hw : ∀ r, ((reader r).value oracle).width ≤ B)
--       (hc : ∀ r, (reader r).work oracle readWork ≤ C) :
--       (queryInitialConeProgramAt sourceLength N P F A a reader q).work oracle readWork ≤
--         queryInitialProgramBitBudget P Amax B C
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.queryInitialProgramBitBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.BitQuery` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval`, `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.queryInitialConeProgramAt` (the published bundle `Def_EditApproxScheme_15`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryChargedFamilyTable_semantic_work_bound` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryInitialProgramCost.lean (declaration OAI.EditApproximation.queryInitialConeProgramAt_work_bound)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
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

theorem queryInitialConeProgramAt_work_bound {ι : Type*} {n : ℕ}
    (sourceLength N P F Amax B C : ℕ) (hP : 0 < P) (A a : BinaryFraction)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B) (hF : Nat.size F ≤ B)
    (hnx : Nat.size sourceLength ≤ B) (hny : Nat.size n ≤ B)
    (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
    (hw : ∀ r, ((reader r).value oracle).width ≤ B)
    (hc : ∀ r, (reader r).work oracle readWork ≤ C) :
    (queryInitialConeProgramAt sourceLength N P F A a reader q).work oracle readWork ≤
      queryInitialProgramBitBudget P Amax B C := by
  sorry

end EditApproximation

end OAI
end
