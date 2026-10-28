-- Prove2me | Theorems.Thm_OAI_Kadison_CompactAverage_exists_stage_average
-- name    : OAI.Kadison.CompactAverage.exists_stage_average
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:32:20.101957+00:00
-- url     : https://prove2.me/theorems/7840376e-2e7a-4c00-bced-0b0ee349c332
-- title:
--   OAI.Kadison.CompactAverage.exists_stage_average: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.CompactAverage`, with `open scoped Topology InnerProductSpace`, `open MeasureTheory MeasureTheory.Measure Filter`):
--
--   ```lean
--   theorem exists_stage_average {ι : Type*} (a : ι → H →L[ℂ] H) (C : ι → ℝ)
--       (hC : ∀ i, 0≤C i)
--       (hb : ∀ n g i, ‖conjugate (U n) Y g * a i-a i*conjugate (U n) Y g‖≤C i)
--       (p q s : H →L[ℂ] H)
--       (hc : ∀ n g, p*(conjugate (U n) Y g*s-s*conjugate (U n) Y g)*q = p*(Y*s-s*Y)*q) :
--       ∃ V : H →L[ℂ] H, ‖V‖≤‖Y‖ ∧
--         (∀ n g, V*(U n g : H →L[ℂ] H)=(U n g : H →L[ℂ] H)*V) ∧
--         (∀ i, ‖V*a i-a i*V‖≤C i) ∧ p*(V*s-s*V)*q=p*(Y*s-s*Y)*q
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.CompactAverage.conjugate` (definitions bundle `OAIQ039C004` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.FreeBlocks.exists_free_symmetrization` of this split imports it.
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

open MeasureTheory MeasureTheory.Measure Filter

namespace Kadison.CompactAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (G : ℕ → Type*) [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
  [∀ n, IsTopologicalGroup (G n)] [∀ n, CompactSpace (G n)]
  [∀ n, MeasurableSpace (G n)] [∀ n, BorelSpace (G n)]

variable (U : ∀ n, G n →* (H ≃ₗᵢ[ℂ] H))
  (hU : ∀ n x, Continuous fun g => U n g x)
  (hnest : ∀ i j, i≤j → ∀ g : G i, ∃ k : G j, U j k=U i g)

variable (μ : ∀ n, Measure (G n)) [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsMulLeftInvariant (μ n)]

variable (Y : H →L[ℂ] H)

include hU hnest μ in
theorem exists_stage_average {ι : Type*} (a : ι → H →L[ℂ] H) (C : ι → ℝ)
    (hC : ∀ i, 0≤C i)
    (hb : ∀ n g i, ‖conjugate (U n) Y g * a i-a i*conjugate (U n) Y g‖≤C i)
    (p q s : H →L[ℂ] H)
    (hc : ∀ n g, p*(conjugate (U n) Y g*s-s*conjugate (U n) Y g)*q = p*(Y*s-s*Y)*q) :
    ∃ V : H →L[ℂ] H, ‖V‖≤‖Y‖ ∧
      (∀ n g, V*(U n g : H →L[ℂ] H)=(U n g : H →L[ℂ] H)*V) ∧
      (∀ i, ‖V*a i-a i*V‖≤C i) ∧ p*(V*s-s*V)*q=p*(Y*s-s*Y)*q := by
  sorry

end Kadison.CompactAverage

end

end
end

end OAI
end
