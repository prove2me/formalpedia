-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_active_commutes
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_commutes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:39:55.101414+00:00
-- url     : https://prove2.me/theorems/e034078b-3dd8-42e9-bfc1-019d77b5d646
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_commutes: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_commutes` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory ContinuousLinearMap`, `open scoped ENNReal`):
--
--   ```lean
--   lemma grouped_active_commutes (hM : M.IsSaturated)
--       (rows cols : TriplePartition I) (n : ℕ) :
--       ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
--         (rowActive M rows.P cols.P cols.A cols.B n e).starProjection ∘L
--           (columnActive M rows.P rows.A rows.B cols.P n e).starProjection =
--         (columnActive M rows.P rows.A rows.B cols.P n e).starProjection ∘L
--           (rowActive M rows.P cols.P cols.A cols.B n e).starProjection
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.TriplePartition`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.amap`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnActive`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleColumnActive`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.instCompleteSpaceSubtypeAEEqFunForallMemFinsetForallArrαYComplexCellLawAddSubgroupLpOfNatENNRealSubmoduleRowActive` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.rowActive` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proofs of `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_line_projection` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness` of this split import it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_active_commutes)

import Mathlib
import Definitions.Def_OAIQ3Ro000

section

attribute [-instance] _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.arrayLaw_probability _root_.OAI.Rokhlin.ArrayObjects.Object.Tower.localLaw_probability
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

lemma grouped_active_commutes (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      (rowActive M rows.P cols.P cols.A cols.B n e).starProjection ∘L
        (columnActive M rows.P rows.A rows.B cols.P n e).starProjection =
      (columnActive M rows.P rows.A rows.B cols.P n e).starProjection ∘L
        (rowActive M rows.P cols.P cols.A cols.B n e).starProjection := by
  sorry
end ArrayObjects.Object.Rolled

open MeasureTheory Set

end Rokhlin

end

end OAI
end
