-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_row_indicators_equal
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:44:48.493328+00:00
-- url     : https://prove2.me/theorems/895a6e88-dd3c-48c3-958f-5f54199fa492
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped BigOperators`):
--
--   ```lean
--   lemma raw_row_indicators_equal (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
--       (a j t : I) (hjt : j ≠ t)
--       (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
--       (hf : ∀ i, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 i py.2))
--       (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
--         ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f p i (plane 0 0 i y) = c) :
--       ∀ᵐ e ∂M.parameterLaw 2,
--         rawSlotIndicator M a (fun p => f p j) (hf j) (plane 1 0 a e) (plane 1 (Fin.last 1) j e) =
--         rawSlotIndicator M a (fun p => f p t) (hf t) (plane 1 0 a e) (plane 1 (Fin.last 1) t e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.instMeasurableSpaceCircle_circleLp`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.plane`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel`, `OAI.Rokhlin.ArrayObjects.Object.parameterLaw` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawSlotIndicator` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal)

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

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

section CircleSlotIndicators

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma raw_row_indicators_equal (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    (a j t : I) (hjt : j ≠ t)
    (f : Arr I M.U 1 → I → Arr I M.Y 0 → Circle)
    (hf : ∀ i, Measurable (fun py : Arr I M.U 1 × Arr I M.Y 0 => f py.1 i py.2))
    (he : ∀ᵐ p ∂M.parameterLaw 1, ∃ c : Circle,
      ∀ᵐ y ∂M.ownKernel 1 p, ∏ i, f p i (plane 0 0 i y) = c) :
    ∀ᵐ e ∂M.parameterLaw 2,
      rawSlotIndicator M a (fun p => f p j) (hf j) (plane 1 0 a e) (plane 1 (Fin.last 1) j e) =
      rawSlotIndicator M a (fun p => f p t) (hf t) (plane 1 0 a e) (plane 1 (Fin.last 1) t e) := by
  sorry

end CircleSlotIndicators

universe u
end ArrayObjects.Object.Rolled

open MeasureTheory Set

end Rokhlin

end

end OAI
end
