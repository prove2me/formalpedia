-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_restricted_fixed_squares
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:43:20.988852+00:00
-- url     : https://prove2.me/theorems/e965f33c-647d-4a7c-a76c-0340f45d9598
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory ContinuousLinearMap`, `open scoped ENNReal`):
--
--   ```lean
--   theorem grouped_restricted_fixed_squares (hM : M.IsSaturated)
--       (rows cols : TriplePartition I) (n : ℕ) :
--       ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
--         let μX := cellLaw M rows.A cols.P n e
--         let μY := cellLaw M rows.B cols.P n e
--         let μC := cellLaw M rows.P cols.A n e
--         let μD := cellLaw M rows.P cols.B n e
--         let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
--         let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
--         let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
--         let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
--         HasFixedInjectiveSquares μX (rectangleRestrictF μX μC μD F K N) ∧
--         HasFixedInjectiveSquares μY (rectangleRestrictG μY μC μD G K N) ∧
--         HasFixedInjectiveSquares μC (rectangleRestrictK μX μY μC F G K) ∧
--         HasFixedInjectiveSquares μD (rectangleRestrictN μX μY μD F G N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.TriplePartition`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₁`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₂`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₃`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₄`, `OAI.Rokhlin.rectangleRestrictF`, `OAI.Rokhlin.rectangleRestrictG`, `OAI.Rokhlin.rectangleRestrictK`, `OAI.Rokhlin.rectangleRestrictN`, `OAI.Rokhlin.rectangleSpace₁`, `OAI.Rokhlin.rectangleSpace₂`, `OAI.Rokhlin.rectangleSpace₃`, `OAI.Rokhlin.rectangleSpace₄`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.amap`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.fibreColumnEdge` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.fibreRowEdge` (definitions bundle `OAIQ3Ro000` of this split); `OAI.Rokhlin.HasFixedInjectiveSquares` (definitions bundle `OAIQ3Ro001` of this split).
--
--   **Used by.** The proofs of `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_b_field` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_data` of this split import it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares)

import Mathlib
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001

section

attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunArrαYOfNatNatComplexMemAddSubgroupLpENNRealSubmoduleRawSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunCellComplexMemAddSubgroupLpOfNatENNRealSubmoduleSlotActive _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallCellSlotTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatForallYRawTupleKernel _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYColumnCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsProbabilityMeasureForallSubtypeMemFinsetArrαYRowCellLaw _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects.Object.Rolled
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_restricted_fixed_squares (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let μX := cellLaw M rows.A cols.P n e
      let μY := cellLaw M rows.B cols.P n e
      let μC := cellLaw M rows.P cols.A n e
      let μD := cellLaw M rows.P cols.B n e
      let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
      let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
      let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
      let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
      HasFixedInjectiveSquares μX (rectangleRestrictF μX μC μD F K N) ∧
      HasFixedInjectiveSquares μY (rectangleRestrictG μY μC μD G K N) ∧
      HasFixedInjectiveSquares μC (rectangleRestrictK μX μY μC F G K) ∧
      HasFixedInjectiveSquares μD (rectangleRestrictN μX μY μD F G N) := by
  sorry
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end
