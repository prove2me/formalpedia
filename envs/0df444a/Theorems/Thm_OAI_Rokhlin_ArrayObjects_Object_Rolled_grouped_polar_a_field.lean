-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_polar_a_field
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:41:56.516004+00:00
-- url     : https://prove2.me/theorems/93c84196-f002-448e-aaa1-38ad28978145
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory ContinuousLinearMap`, `open scoped ENNReal`):
--
--   ```lean
--   theorem grouped_polar_a_field (hM : M.IsSaturated)
--       (rows cols : TriplePartition I) (n : ℕ) :
--       ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
--         ∀ R : GroupedPolarData M rows cols n e,
--           commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e ≤
--             lpMeas ℂ ℂ (MeasurableSpace.comap R.a.unitary inferInstance) 2
--               (cellLaw M rows.A cols.P n e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.TriplePartition`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₁`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₂`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₃`, `OAI.Rokhlin.instCompleteSpaceSubtypeMemSubmoduleComplexRectangleSpace₄`, `OAI.Rokhlin.rectangleRestrictF`, `OAI.Rokhlin.rectangleRestrictG`, `OAI.Rokhlin.rectangleRestrictK`, `OAI.Rokhlin.rectangleRestrictN`, `OAI.Rokhlin.rectangleSpace₁`, `OAI.Rokhlin.rectangleSpace₂`, `OAI.Rokhlin.rectangleSpace₃`, `OAI.Rokhlin.rectangleSpace₄`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.amap`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.instStandardBorelSpaceα`, `OAI.Rokhlin.MeasurablePolar`, `OAI.Rokhlin.MeasurablePolarRectangle`, `OAI.Rokhlin.StrongUnitary.measurableSpace`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.GroupedPolarData`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cells`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.commonActive`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.fibreColumnEdge`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.fibreRowEdge`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.groupMarginal`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.groupMarginal_markov`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.instFactNeENNRealOfNatTop_10` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.instFactNeENNRealOfNatTop_3` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_polar_a_field)

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

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal

namespace ArrayObjects.Object.Rolled
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

attribute [local instance] OAI.Rokhlin.ArrayObjects.Object.Rolled.instFactNeENNRealOfNatTop_10
theorem grouped_polar_a_field (hM : M.IsSaturated)
    (rows cols : TriplePartition I) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      ∀ R : GroupedPolarData M rows cols n e,
        commonActive M rows.A rows.P rows.B cols.P cols.A cols.B n e ≤
          lpMeas ℂ ℂ (MeasurableSpace.comap R.a.unitary inferInstance) 2
            (cellLaw M rows.A cols.P n e) := by
  sorry

end ArrayObjects.Object.Rolled
end

end Rokhlin

end

end OAI
end
