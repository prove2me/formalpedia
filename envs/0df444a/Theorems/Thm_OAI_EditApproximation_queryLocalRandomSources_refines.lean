-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryLocalRandomSources_refines
-- name    : OAI.EditApproximation.queryLocalRandomSources_refines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:30:14.211333+00:00
-- url     : https://prove2.me/theorems/9cf35c6d-ced6-4503-b17b-89b649331226
-- title:
--   OAI.EditApproximation.queryLocalRandomSources_refines: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryLocalRandomSources_refines` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSources.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSources.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem queryLocalRandomSources_refines
--       (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
--       (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
--       (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
--       (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
--       (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
--         (readGroup key) (expectedGroup key))
--       (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
--         (readInteger key range) (expectedInteger key range))
--       (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
--         (readEarlier key) (expectedEarlier key))
--       (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
--         (readCurrent key) (expectedCurrent key)) :
--       BitQuery.Refines (fun word value => word.value = value)
--         (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
--           tau a eta kappa delta t parentInitial child initial R hc hi q
--           readGroup readInteger readEarlier readCurrent)
--         (localRandomSourceStepQuery source target parent N P F exponent H Q
--           tau.value a.value eta.value kappa.value delta.value t
--           (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
--           (fun i r => (initial i r).1.value) q
--           expectedGroup expectedInteger expectedEarlier expectedCurrent)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryLocalRandomSources` and `OAI.EditApproximation.BitQuery.Refines` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BitQuery` and `OAI.EditApproximation.FiniteQuery` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.GroupScalarKey` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.localRandomSourceStepQuery` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proof of `OAI.EditApproximation.queryFamilyBoundedActive_refines` of this split imports it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryLocalSources.lean (declaration OAI.EditApproximation.queryLocalRandomSources_refines)

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

theorem queryLocalRandomSources_refines
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range))
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial child initial R hc hi q
        readGroup readInteger readEarlier readCurrent)
      (localRandomSourceStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value) q
        expectedGroup expectedInteger expectedEarlier expectedCurrent) := by
  sorry

end Sources
end EditApproximation

end OAI
end
