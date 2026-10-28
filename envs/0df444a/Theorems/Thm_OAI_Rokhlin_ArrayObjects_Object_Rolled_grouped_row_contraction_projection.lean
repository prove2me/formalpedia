-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_row_contraction_projection
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_row_contraction_projection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:48:14.451727+00:00
-- url     : https://prove2.me/theorems/ce7f913a-01a2-4c96-9902-b0680539f5aa
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_row_contraction_projection: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_row_contraction_projection` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory ContinuousLinearMap`, `open scoped ENNReal`):
--
--   ```lean
--   theorem grouped_row_contraction_projection (hM : M.IsSaturated)
--       (rows cols : TriplePartition I) (n : ℕ) :
--       ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
--         ∀ (hr : MeasurePreserving (cells M rows.P cols.P n) (M.ownKernel (n+2) e) (cellLaw M rows.P cols.P n e))
--         (hst : MeasurePreserving (fun y => (cells M rows.P cols.A n y,cells M rows.P cols.B n y))
--           (M.ownKernel (n+2) e) ((cellLaw M rows.P cols.A n e).prod (cellLaw M rows.P cols.B n e)))
--         (g : Lp ℂ 2 (cellLaw M rows.P cols.A n e)) (h : Lp ℂ 2 (cellLaw M rows.P cols.B n e)),
--         (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection
--           (JoiningOperator.contraction hr hst g h) =
--         JoiningOperator.contraction hr hst
--           ((commonActive M rows.P rows.A rows.B cols.A cols.P cols.B n e).starProjection g)
--           ((commonActive M rows.P rows.A rows.B cols.B cols.P cols.A n e).starProjection h)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.TriplePartition`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.amap`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cells`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.commonActive`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.groupMarginal`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.groupMarginal_markov` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleCommonActive` (definitions bundle `OAIQ3Ro000` of this split); `OAI.Rokhlin.JoiningOperator.contraction` (definitions bundle `OAIQ3Ro002` of this split).
--
--   **Used by.** The proofs of `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_b_field` of this split import it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_row_contraction_projection)

import Mathlib
import Definitions.Def_OAIQ3Ro002

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

section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

theorem grouped_row_contraction_projection (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ (hr : MeasurePreserving (cells M rows.P cols.P n) (M.ownKernel (n+2) e) (cellLaw M rows.P cols.P n e))
      (hst : MeasurePreserving (fun y => (cells M rows.P cols.A n y,cells M rows.P cols.B n y))
        (M.ownKernel (n+2) e) ((cellLaw M rows.P cols.A n e).prod (cellLaw M rows.P cols.B n e)))
      (g : Lp ℂ 2 (cellLaw M rows.P cols.A n e)) (h : Lp ℂ 2 (cellLaw M rows.P cols.B n e)),
      (commonActive M rows.P rows.A rows.B cols.P cols.A cols.B n e).starProjection
        (JoiningOperator.contraction hr hst g h) =
      JoiningOperator.contraction hr hst
        ((commonActive M rows.P rows.A rows.B cols.A cols.P cols.B n e).starProjection g)
        ((commonActive M rows.P rows.A rows.B cols.B cols.P cols.A n e).starProjection h) := by
  sorry

end

universe u

end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end
