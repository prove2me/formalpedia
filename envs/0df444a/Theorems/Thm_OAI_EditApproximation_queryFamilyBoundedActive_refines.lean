-- Prove2me | Theorems.Thm_OAI_EditApproximation_queryFamilyBoundedActive_refines
-- name    : OAI.EditApproximation.queryFamilyBoundedActive_refines
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:35:11.043943+00:00
-- url     : https://prove2.me/theorems/16e71824-53d7-45ff-b280-44f4e2127462
-- title:
--   OAI.EditApproximation.queryFamilyBoundedActive_refines: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.queryFamilyBoundedActive_refines` of [lean/OAI/Combinatorics/EditApproximation/Queries/QueryFamilyActive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryFamilyActive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--   theorem queryFamilyBoundedActive_refines (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
--       (initial : PhysicalEntry M J target.length → ℕ)
--       (ha : a.value = refinementFactor (factor parent.val.pass) F)
--       (hlong : ¬ (physicalSourceInterval source.length parent.val.node).hi -
--         (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
--       BitQuery.Refines (fun word value => word.value = value)
--         (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
--           T S passes copies parent hindex hbelow)
--         (physicalRandomBoundedQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies factor multiplier
--           tau.value eta.value kappa.value delta.value
--           (physicalFamilyGroupRead target N P F exponent H Q passes copies)
--           (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial parent)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.queryFamilyBoundedActive` and `OAI.EditApproximation.BitQuery.Refines` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.BinaryFraction` and `OAI.EditApproximation.refinementFactor` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.TreeLayer` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` and `OAI.EditApproximation.physicalSourceInterval` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.PhysicalTableRequest`, `OAI.EditApproximation.PhysicalTableRequest.Bounded` and `OAI.EditApproximation.PhysicalTableRequest.combinedRank` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.PhysicalFamilyScalarKey`, `OAI.EditApproximation.physicalFamilyGroupRead`, `OAI.EditApproximation.physicalFamilyOnlineRead` and `OAI.EditApproximation.physicalRandomBoundedQuery` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedQueryMemoNormalized_correct` and `OAI.EditApproximation.computedQueryMemoNormalized_width` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Queries/QueryFamilyActive.lean (declaration OAI.EditApproximation.queryFamilyBoundedActive_refines)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Bounded
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (T S passes copies : ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded (passes + 1) copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)

theorem queryFamilyBoundedActive_refines (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ)
    (ha : a.value = refinementFactor (factor parent.val.pass) F)
    (hlong : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyBoundedActive (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
        T S passes copies parent hindex hbelow)
      (physicalRandomBoundedQuery (R := R) source target N P F exponent H Q T S (passes + 1) copies factor multiplier
        tau.value eta.value kappa.value delta.value
        (physicalFamilyGroupRead target N P F exponent H Q passes copies)
        (physicalFamilyOnlineRead target N P F exponent H Q passes copies) initial parent) := by
  sorry

end Bounded
end EditApproximation

end OAI
end
