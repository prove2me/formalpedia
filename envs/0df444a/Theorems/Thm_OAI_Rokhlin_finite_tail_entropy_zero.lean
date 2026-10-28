-- Prove2me | Theorems.Thm_OAI_Rokhlin_finite_tail_entropy_zero
-- name    : OAI.Rokhlin.finite_tail_entropy_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:37:57.722523+00:00
-- url     : https://prove2.me/theorems/6fbfec84-69bd-40e0-862d-cffbc849e972
-- title:
--   OAI.Rokhlin.finite_tail_entropy_zero: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.finite_tail_entropy_zero` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin`, with `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem finite_tail_entropy_zero (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
--       (a : Ω → A) (ha : Measurable a) (b : Ω → B) (hb : Measurable[observableTail μ T a] b) :
--       Tendsto (fun n : ℕ => randomEntropy μ (fun x => fun i : Fin n => b ((T^[i.val]) x)) / n)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.observableTail` and `OAI.Rokhlin.randomEntropy` (definitions bundle `OAIQ3Ro001` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.tail_finite_correlation_zero` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tail.lean (declaration OAI.Rokhlin.finite_tail_entropy_zero)

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
open scoped Topology
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem finite_tail_entropy_zero (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (a : Ω → A) (ha : Measurable a) (b : Ω → B) (hb : Measurable[observableTail μ T a] b) :
    Tendsto (fun n : ℕ => randomEntropy μ (fun x => fun i : Fin n => b ((T^[i.val]) x)) / n)
      atTop (𝓝 0) := by
  sorry
end

open MeasureTheory Filter
open scoped Topology BigOperators

end Rokhlin

end

end OAI
end
