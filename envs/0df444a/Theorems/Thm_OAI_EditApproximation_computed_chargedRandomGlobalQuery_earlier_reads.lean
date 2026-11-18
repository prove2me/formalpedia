-- Prove2me | Theorems.Thm_OAI_EditApproximation_computed_chargedRandomGlobalQuery_earlier_reads
-- name    : OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:08.330229+00:00
-- url     : https://prove2.me/theorems/818baf13-64cd-4b13-9b9c-c033475eac53
-- title:
--   OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedChargedRandomBudget.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedChargedRandomBudget.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--    theorem computed_chargedRandomGlobalQuery_earlier_reads
--       (request : ChargedPhysicalRequest M J target.length passes copies T S) :
--       (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
--         H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
--         readGroup readInteger initial request).cost
--         (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
--           H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
--           group integer initial child.val))
--         (Sum.elim (fun _ => 0) (fun child => chargedEarlierWeight request child.val)) ≤
--           inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.chargedEarlierWeight` and `OAI.EditApproximation.FiniteQuery.cost` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.chargedRequestValue` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.FiniteQuery`, `OAI.EditApproximation.coarseExponent`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.PhysicalInternalNode` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.CellGroupDraws` and `OAI.EditApproximation.GroupScalarKey` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.chargedRandomGlobalQuery` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedFamilyTree_valid` and `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedChargedRandomBudget.lean (declaration OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Current

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "values" => localRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
    tau eta kappa delta group integer initial

variable (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M)
  (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
  (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
  (hS : S = (integerParameters N).S)

variable (hcopies : copies ≤ inputHeight N ^ 2)
  (hAmin : ∀ pass, 1 ≤ factor pass)

include hN hell hM hAmax hP hT hS hcopies hAmin in
 theorem computed_chargedRandomGlobalQuery_earlier_reads
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
        group integer initial child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedEarlierWeight request child.val)) ≤
        inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  sorry

end Current

end EditApproximation

end OAI
end
