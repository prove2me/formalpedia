-- Prove2me | Theorems.Thm_OAI_Kadison_CompactAverage_exists_average
-- name    : OAI.Kadison.CompactAverage.exists_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:32:18.412819+00:00
-- url     : https://prove2.me/theorems/03055ca5-bf0f-4004-99d8-7fc5704d44f5
-- title:
--   OAI.Kadison.CompactAverage.exists_average: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CompactAverage`, with `open scoped Topology InnerProductSpace`, `open MeasureTheory MeasureTheory.Measure`):
--
--   ```lean
--   theorem exists_average (μ : Measure G) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ] :
--       ∃ V : H →L[ℂ] H, ‖V‖ ≤ ‖Y‖ ∧
--         (∀ g, V * (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) * V) ∧
--         (∀ x y, inner ℂ (V x) y = ∫ g, inner ℂ (conjugate U Y g x) y ∂μ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CompactAverage.conjugate` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.CompactAverage.exists_stage_average`, `OAI.Kadison.RepresentedTower.exists_tower_average` and `OAI.Kadison.uniform_commutator_finiteDimensional` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C004

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure

namespace Kadison.CompactAverage

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ x : H, Continuous fun g => U g x)

variable (Y : H →L[ℂ] H)

include hU in
theorem exists_average (μ : Measure G) [IsProbabilityMeasure μ] [IsMulLeftInvariant μ] :
    ∃ V : H →L[ℂ] H, ‖V‖ ≤ ‖Y‖ ∧
      (∀ g, V * (U g : H →L[ℂ] H) = (U g : H →L[ℂ] H) * V) ∧
      (∀ x y, inner ℂ (V x) y = ∫ g, inner ℂ (conjugate U Y g x) y ∂μ) := by
  sorry

end Kadison.CompactAverage

end

end
end

end OAI
end
