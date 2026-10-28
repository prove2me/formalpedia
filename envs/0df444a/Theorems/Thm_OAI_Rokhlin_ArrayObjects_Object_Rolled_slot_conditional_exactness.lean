-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_slot_conditional_exactness
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:45:08.784854+00:00
-- url     : https://prove2.me/theorems/6206d193-e2b0-4305-b843-b27a4442293e
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open Set MeasureTheory ProbabilityTheory`, `open scoped ENNReal BigOperators`):
--
--   ```lean
--   theorem slot_conditional_exactness (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
--       (i : I) (s : ComplementSplit ({i} : Finset I)) :
--       ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
--         slotActive M i (slotLocal M i u) p ≤ slotExactSpan M i (slotLocal M i u) p
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.ComplementSplit`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.parameterCoordinateKernel`, `OAI.Rokhlin.ArrayObjects.Object.parameterLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.Cell`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.instIsMarkovKernelArrαUOfNatNatCellSlotLocal`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.slotActive`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.slotExactSpan` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.slotLocal` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_forces_coefficient` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness)

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

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

section PairTransport

theorem slot_conditional_exactness (hM : M.IsSaturated) (hI : 2 ≤ Fintype.card I)
    (i : I) (s : ComplementSplit ({i} : Finset I)) :
    ∀ᵐ u ∂M.parameterLaw 0, ∀ᵐ p ∂M.parameterCoordinateKernel i u,
      slotActive M i (slotLocal M i u) p ≤ slotExactSpan M i (slotLocal M i u) p := by
  sorry
end PairTransport

end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end
