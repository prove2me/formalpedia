-- Prove2me | Theorems.Thm_OAI_EditApproximation_computed_localRandomDataQuery_table_cost
-- name    : OAI.EditApproximation.computed_localRandomDataQuery_table_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:29:45.369592+00:00
-- url     : https://prove2.me/theorems/6fc45dc3-50fd-4b4a-87d6-45019a513fd7
-- title:
--   OAI.EditApproximation.computed_localRandomDataQuery_table_cost: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computed_localRandomDataQuery_table_cost` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedRandomTableCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedRandomTableCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`):
--
--   ```lean
--    theorem computed_localRandomDataQuery_table_cost {ι α : Type*} (source target : List α)
--       {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P H T t : ℕ)
--       (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
--       (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
--       (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
--       (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
--       (readParent : TargetInterval target.length → FiniteQuery ι)
--       (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
--       (readGroup : GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery ι)
--       (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
--       (q : TargetInterval target.length)
--       (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
--       (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
--       (oracle : ι → ℚ) (weight : ι → ℕ) (dataCost earlierCost currentCost : ℕ)
--       (hparent : ∀ r, (readParent r).cost oracle weight ≤ dataCost)
--       (hmass : ∀ key, (readMass key).cost oracle weight ≤ T * dataCost)
--       (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ dataCost)
--       (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
--       (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
--       (hearlier : ∀ key, (readEarlier key).cost oracle weight ≤ earlierCost)
--       (hcurrent : ∀ key, (readCurrent key).cost oracle weight ≤ currentCost)
--       (hw : 0 ≤ (readParent q).value oracle) :
--       let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
--       (localRandomDataQuery source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
--         H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta t
--         readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
--           (2 + 2 * B) * dataCost + B * earlierCost +
--             (2 * M * inputSmallLog N ^ 256) * currentCost
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.FiniteQuery.cost` and `OAI.EditApproximation.FiniteQuery.value` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.FiniteQuery`, `OAI.EditApproximation.coarseExponent`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.refinementFactor`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.TargetInterval` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.GroupScalarKey` (the published bundle `Def_EditApproxScheme_13`); `OAI.EditApproximation.localRandomDataQuery` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedFamilyTree_valid`, `OAI.EditApproximation.computedPhysicalCoarseWork_expected_le` and `OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedRandomTableCost.lean (declaration OAI.EditApproximation.computed_localRandomDataQuery_table_cost)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_localRandomDataQuery_table_cost {ι α : Type*} (source target : List α)
    {M : ℕ} [NeZero M] (parent : TargetInterval source.length) (N P H T t : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
    (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
    (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (readParent : TargetInterval target.length → FiniteQuery ι)
    (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
    (readGroup : GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery ι)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (q : TargetInterval target.length)
    (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (oracle : ι → ℚ) (weight : ι → ℕ) (dataCost earlierCost currentCost : ℕ)
    (hparent : ∀ r, (readParent r).cost oracle weight ≤ dataCost)
    (hmass : ∀ key, (readMass key).cost oracle weight ≤ T * dataCost)
    (hinitial : ∀ key, (readInitial key).cost oracle weight ≤ dataCost)
    (hgroup : ∀ key, (readGroup key).cost oracle weight = 0)
    (honline : ∀ key range, (readInteger key range).cost oracle weight = 0)
    (hearlier : ∀ key, (readEarlier key).cost oracle weight ≤ earlierCost)
    (hcurrent : ∀ key, (readCurrent key).cost oracle weight ≤ currentCost)
    (hw : 0 ≤ (readParent q).value oracle) :
    let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
    (localRandomDataQuery source target parent N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
        (2 + 2 * B) * dataCost + B * earlierCost +
          (2 * M * inputSmallLog N ^ 256) * currentCost := by
  sorry

end EditApproximation

end OAI
end
