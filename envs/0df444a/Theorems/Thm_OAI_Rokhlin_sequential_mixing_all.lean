-- Prove2me | Theorems.Thm_OAI_Rokhlin_sequential_mixing_all
-- name    : OAI.Rokhlin.sequential_mixing_all
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:38:13.043715+00:00
-- url     : https://prove2.me/theorems/eed44740-1ee0-4529-b867-be41ca9e47b2
-- title:
--   OAI.Rokhlin.sequential_mixing_all: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.sequential_mixing_all` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ENNReal`):
--
--   ```lean
--   theorem sequential_mixing_all (μ : Measure Ω) [IsProbabilityMeasure μ]
--       (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
--       (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
--         Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) :
--       ∀ k, SequentialMixing μ T k
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.SequentialMixing` (definitions bundle `OAIQ3Ro001` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.mixing_all_finite_orders` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Main.lean (declaration OAI.Rokhlin.sequential_mixing_all)

import Mathlib
import Definitions.Def_OAIQ3Ro001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem sequential_mixing_all (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t))) :
    ∀ k, SequentialMixing μ T k := by
  sorry
end

open MeasureTheory Filter

end Rokhlin

end

end OAI
end
