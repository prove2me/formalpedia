-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_raw_row_active_to_column_exact
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:44:08.206803+00:00
-- url     : https://prove2.me/theorems/2b757a19-7d6d-488c-8708-15997f012ab3
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators`):
--
--   ```lean
--   lemma raw_row_active_to_column_exact (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (a j : I) :
--       ∀ᵐ e ∂M.parameterLaw 2, ∀ (f : I → Arr I M.Y 0 → Circle)
--         (hf : ∀ i, Measurable (f i)) (c : Circle),
--         (∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) →
--         let ν := M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))
--         let v := circleLp ν (f j) (hf j)
--         v ∈ rawSlotActive M a ν (plane 1 (Fin.last 1) j e) →
--         v ∈ rawExactCone M a ν (plane 1 (Fin.last 1) j e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.circleLp`, `OAI.Rokhlin.instMeasurableSpaceCircle_circleLp`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.plane`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel`, `OAI.Rokhlin.ArrayObjects.Object.ownKernel_markov`, `OAI.Rokhlin.ArrayObjects.Object.parameterLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawExactCone` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.rawSlotActive` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact)

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

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ArrayObjects.Object.Rolled

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma raw_row_active_to_column_exact (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (a j : I) :
    ∀ᵐ e ∂M.parameterLaw 2, ∀ (f : I → Arr I M.Y 0 → Circle)
      (hf : ∀ i, Measurable (f i)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 (plane 1 0 a e), ∏ i, f i (plane 0 0 i y) = c) →
      let ν := M.ownKernel 0 (plane 0 0 j (plane 1 0 a e))
      let v := circleLp ν (f j) (hf j)
      v ∈ rawSlotActive M a ν (plane 1 (Fin.last 1) j e) →
      v ∈ rawExactCone M a ν (plane 1 (Fin.last 1) j e) := by
  sorry

end ArrayObjects.Object.Rolled
end

open MeasureTheory Set

end Rokhlin

end

end OAI
end
