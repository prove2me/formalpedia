-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_active_intersections
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_intersections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:41:31.163189+00:00
-- url     : https://prove2.me/theorems/25b55899-b7e5-40d6-93f8-13f4888d5dc4
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_intersections: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_intersections` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory ContinuousLinearMap`, `open scoped ENNReal`):
--
--   ```lean
--   theorem grouped_active_intersections (hM : M.IsSaturated)
--       (rows cols : TriplePartition I) (n : ℕ) :
--       ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
--         let D₁ := commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e
--         let D₂ := commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e
--         let D₃ := commonActive M rows.B rows.P rows.A cols.A cols.P cols.B n e
--         let D₄ := commonActive M rows.B rows.P rows.A cols.B cols.P cols.A n e
--         let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
--         let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
--         let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
--         let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
--         (∀ᵐ r ∂cellLaw M rows.A cols.P n e, D₁.starProjection ∘L F r = F r ∘L D₂.starProjection) ∧
--         (∀ᵐ r ∂cellLaw M rows.B cols.P n e, D₃.starProjection ∘L G r = G r ∘L D₄.starProjection) ∧
--         (∀ᵐ r ∂cellLaw M rows.P cols.A n e, D₁.starProjection ∘L K r = K r ∘L D₃.starProjection) ∧
--         (∀ᵐ r ∂cellLaw M rows.P cols.B n e, D₂.starProjection ∘L N r = N r ∘L D₄.starProjection)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.TriplePartition`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.amap`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.commonActive`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.fibreColumnEdge`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.fibreRowEdge` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proofs of `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_column_contraction_projection`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_b_field`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_row_contraction_projection` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal` of this split import it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_intersections)

import Mathlib
import Definitions.Def_OAIQ3Ro000

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

theorem grouped_active_intersections (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      let D₁ := commonActive M rows.A rows.P rows.B cols.A cols.P cols.B n e
      let D₂ := commonActive M rows.A rows.P rows.B cols.B cols.P cols.A n e
      let D₃ := commonActive M rows.B rows.P rows.A cols.A cols.P cols.B n e
      let D₄ := commonActive M rows.B rows.P rows.A cols.B cols.P cols.A n e
      let F := fibreRowEdge M rows.A cols.P cols.A cols.B n e
      let G := fibreRowEdge M rows.B cols.P cols.A cols.B n e
      let K := fibreColumnEdge M rows.P rows.A rows.B cols.A n e
      let N := fibreColumnEdge M rows.P rows.A rows.B cols.B n e
      (∀ᵐ r ∂cellLaw M rows.A cols.P n e, D₁.starProjection ∘L F r = F r ∘L D₂.starProjection) ∧
      (∀ᵐ r ∂cellLaw M rows.B cols.P n e, D₃.starProjection ∘L G r = G r ∘L D₄.starProjection) ∧
      (∀ᵐ r ∂cellLaw M rows.P cols.A n e, D₁.starProjection ∘L K r = K r ∘L D₃.starProjection) ∧
      (∀ᵐ r ∂cellLaw M rows.P cols.B n e, D₂.starProjection ∘L N r = N r ∘L D₄.starProjection) := by
  sorry

end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end
