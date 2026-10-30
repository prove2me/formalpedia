-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_Object_Rolled_saturated_correlation_zero
-- name    : OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:45:09.709411+00:00
-- url     : https://prove2.me/theorems/aa6b3979-2777-46c2-83f5-6a3e2c4469d1
-- title:
--   OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects.Object.Rolled`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Topology BigOperators`):
--
--   ```lean
--   lemma saturated_correlation_zero (i : I) (f : I → Arr I M.Y 0 → ℂ)
--       (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
--       (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
--       (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.ArrayObjects.Arr`, `OAI.Rokhlin.ArrayObjects.Index`, `OAI.Rokhlin.ArrayObjects.InitialLaws`, `OAI.Rokhlin.ArrayObjects.Object`, `OAI.Rokhlin.ArrayObjects.StandardSpace`, `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα`, `OAI.Rokhlin.ArrayObjects.plane`, `OAI.Rokhlin.ArrayObjects.zeroEquiv`, `OAI.Rokhlin.ArrayObjects.Object.IsSaturated` and `OAI.Rokhlin.ArrayObjects.Object.localLaw` (definitions bundle `OAIQ3Ro000` of this split); `OAI.Rokhlin.wordEntropy` (definitions bundle `OAIQ3Ro001` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean (declaration OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero)

import Mathlib
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)
    (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : M.localLaw.map M.x = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hM hk hμ hT hmix hα hcenter hH in
lemma saturated_correlation_zero (i : I) (f : I → Arr I M.Y 0 → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α (M.x (zeroEquiv I M.Y y)))) :
    (∫ y, ∏ j, f j (plane 0 0 j y) ∂M.law 1) = 0 := by
  sorry
end ArrayObjects.Object.Rolled

end Rokhlin

end

end OAI
end
