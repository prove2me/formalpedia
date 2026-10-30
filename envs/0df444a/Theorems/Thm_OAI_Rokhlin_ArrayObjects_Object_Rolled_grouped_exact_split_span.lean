-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_grouped_exact_split_span
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:40:44.399572+00:00
-- url     : https://prove2.me/theorems/9f5677d8-be3c-4f1e-9467-b7b9914c763f
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal InnerProductSpace`):
--
--   ```lean
--   lemma grouped_exact_split_span (hM : M.IsSaturated) (P R : Finset I)
--       (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
--       ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
--         (Submodule.span ℂ (rowSplitExact M P R t n e ∩ columnSplitExact M P R s n e)).topologicalClosure =
--           commonActive M P s.A s.B R t.A t.B n e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.ComplementSplit`, `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.amap`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.cellLaw`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.columnSplitExact`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.commonActive` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.rowSplitExact` (definitions bundle `OAIQ3Ro000` of this split).
--
--   **Used by.** The proofs of `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_active_to_column_exact`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_indicators_equal`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_row_line_projection` and `OAI.Rokhlin.ArrayObjects.Object.Rolled.slot_conditional_exactness` of this split import it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_exact_split_span)

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

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma grouped_exact_split_span (hM : M.IsSaturated) (P R : Finset I)
    (s : ComplementSplit P) (t : ComplementSplit R) (n : ℕ) :
    ∀ᵐ e ∂(M.law (n+2)).map (amap M.par (n+2)),
      (Submodule.span ℂ (rowSplitExact M P R t n e ∩ columnSplitExact M P R s n e)).topologicalClosure =
        commonActive M P s.A s.B R t.A t.B n e := by
  sorry

end ArrayObjects.Object.Rolled

open MeasureTheory Set

end Rokhlin

end

end OAI
end
