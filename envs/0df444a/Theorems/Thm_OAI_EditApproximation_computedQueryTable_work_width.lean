-- Prove2me | Theorems.Thm_OAI_EditApproximation_computedQueryTable_work_width
-- name    : OAI.EditApproximation.computedQueryTable_work_width
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:58.593833+00:00
-- url     : https://prove2.me/theorems/d7310656-66d9-4285-a49c-7f65a1761659
-- title:
--   OAI.EditApproximation.computedQueryTable_work_width: intermediate lemma from OpenAI, An Almost-Linear Approximation Scheme for Edit Distance
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.EditApproximation.almostLinearEditDistanceRawBandV3`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An Almost-Linear Approximation Scheme for Edit Distance*, OpenAI Math Release, September 24, 2026, result family 121, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.EditApproximation.computedQueryTable_work_width` of [lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableWork.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableWork.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.EditApproximation`, with `open Filter BinaryFraction`):
--
--   ```lean
--   theorem computedQueryTable_work_width :
--       ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
--         ∀ (input : ComputedFamilyInput source target N)
--         (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
--         symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
--         ∀ (parent : ComputedQueryTableParent source target N)
--         (oracle : ComputedQueryTableKey source target N parent → BinaryFraction),
--         (∀ key, (oracle key).width ≤ inputHeight N ^ 3) →
--         (∀ child, (oracle (Sum.inr child)).value = computedFamilyTableValue source target N input child.val) →
--         (computedQueryTableProgram source target N occurrence symbolBits positionBits parent).work
--           oracle (fun _ => 1) ≤ computedLocalKernelBudget computedTableQueryDegree N ∧
--         ((computedQueryTableProgram source target N occurrence symbolBits positionBits parent).value oracle).width ≤
--           localWarmupWordBudget (integerParameters N).M (inputHeight N ^ 8) +
--             preparedKernelWordBudget (integerParameters N).M (inputHeight N ^ 8)
--   ```
--
--   **Definitions.** The statement is written with `OAI.EditApproximation.BinaryFraction.localWarmupWordBudget` and `OAI.EditApproximation.BinaryFraction.preparedKernelWordBudget` (definitions bundle `OAIQ361V3Ea000` of this split); `OAI.EditApproximation.computedLocalKernelBudget` (definitions bundle `OAIQ361V3Ea001` of this split); `OAI.EditApproximation.ComputedQueryTableKey`, `OAI.EditApproximation.ComputedQueryTableParent`, `OAI.EditApproximation.computedFamilyTableValue`, `OAI.EditApproximation.computedQueryTableProgram` and `OAI.EditApproximation.computedTableQueryDegree` (definitions bundle `OAIQ361V3Ea002` of this split); `OAI.EditApproximation.BinaryFraction`, `OAI.EditApproximation.BinaryMemo`, `OAI.EditApproximation.PositionCounts`, `OAI.EditApproximation.computedSeedPassCount`, `OAI.EditApproximation.inputHeight`, `OAI.EditApproximation.inputSmallLog`, `OAI.EditApproximation.integerParameters`, `OAI.EditApproximation.smallLogExponent` and `OAI.EditApproximation.IntegerParameters` (the published bundle `Def_EditApproxScheme_01`); `OAI.EditApproximation.intervalTreeDepth` (the published bundle `Def_EditApproxScheme_02`); `OAI.EditApproximation.BinaryFraction.width` (the published bundle `Def_EditApproxScheme_03`); `OAI.EditApproximation.BinaryFraction.value` (the published bundle `Def_EditApproxScheme_04`); `OAI.EditApproximation.BitQuery.value` and `OAI.EditApproximation.BitQuery.work` (the published bundle `Def_EditApproxScheme_05`); `OAI.EditApproximation.PhysicalEntry` (the published bundle `Def_EditApproxScheme_06`); `OAI.EditApproximation.ChargedPhysicalRequest`, `OAI.EditApproximation.PhysicalTableRequest` and `OAI.EditApproximation.PhysicalTableRequest.Bounded` (the published bundle `Def_EditApproxScheme_08`); `OAI.EditApproximation.ChargedPhysicalRequest.rank` (the published bundle `Def_EditApproxScheme_11`); `OAI.EditApproximation.ComputedFamilyInput` and `OAI.EditApproximation.PhysicalFamilyScalarKey` (the published bundle `Def_EditApproxScheme_14`).
--
--   **Used by.** The proofs of `OAI.EditApproximation.computedQueryTemporaryCells_polynomial` and `OAI.EditApproximation.integerBinaryWork_expected_near_linear` of this split import it.
-- source:
--   OpenAI, An Almost-Linear Approximation Scheme for Edit Distance, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 121; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-Almost-Linear-Approximation-Scheme-for-Edit-Distance-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/EditApproximation/Refinement/ComputedQueryTableWork.lean (declaration OAI.EditApproximation.computedQueryTable_work_width)

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002

section

attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] queryChargedFamilyTable localRequestValue

theorem computedQueryTable_work_width :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      ∀ (parent : ComputedQueryTableParent source target N)
      (oracle : ComputedQueryTableKey source target N parent → BinaryFraction),
      (∀ key, (oracle key).width ≤ inputHeight N ^ 3) →
      (∀ child, (oracle (Sum.inr child)).value = computedFamilyTableValue source target N input child.val) →
      (computedQueryTableProgram source target N occurrence symbolBits positionBits parent).work
        oracle (fun _ => 1) ≤ computedLocalKernelBudget computedTableQueryDegree N ∧
      ((computedQueryTableProgram source target N occurrence symbolBits positionBits parent).value oracle).width ≤
        localWarmupWordBudget (integerParameters N).M (inputHeight N ^ 8) +
          preparedKernelWordBudget (integerParameters N).M (inputHeight N ^ 8) := by
  sorry

end EditApproximation

end OAI
end
