-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_SieveExponent_recurrence
-- name    : OAI.CubicFirstMoment.SieveExponent.recurrence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:38:39.911865+00:00
-- url     : https://prove2.me/theorems/b0c30d97-0a35-4e20-9823-09ee5b63e355
-- title:
--   OAI.CubicFirstMoment.SieveExponent.recurrence: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.SieveExponent.recurrence` of [lean/OAI/NumberTheory/CubicGram/QuantitativeRecurrence.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicGram/QuantitativeRecurrence.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   lemma SieveExponent.recurrence {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
--       (hExp : SieveExponent ξ) {ε : ℝ} (hε : 0 < ε) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
--         (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
--         (∀ x ∈ H, primary x ∧ norm x ≤ M) →
--         finiteCubicBound S H ≤ C*(M*N)^ε*sieveRecurrenceShape ξ M N
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.sieveRecurrenceShape` (definitions bundle `OAIQ096A003` of this split); `OAI.CubicFirstMoment.SieveExponent` and `OAI.CubicFirstMoment.finiteCubicBound` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.sieveExponent_four_thirds` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicGram/QuantitativeRecurrence.lean (declaration OAI.CubicFirstMoment.SieveExponent.recurrence)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A003
import Definitions.Def_OAIQ096A005

section

attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma SieveExponent.recurrence {ξ : ℝ} (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hExp : SieveExponent ξ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (M N : ℝ), 1 ≤ N → N ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ x ∈ H, primary x ∧ norm x ≤ M) →
      finiteCubicBound S H ≤ C*(M*N)^ε*sieveRecurrenceShape ξ M N := by
  sorry

end CubicFirstMoment
end
end

end OAI
end
