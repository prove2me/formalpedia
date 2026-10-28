-- Prove2me | Theorems.Thm_OAI_Kadison_exists_countable_strong_contraction_tests
-- name    : OAI.Kadison.exists_countable_strong_contraction_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:22.810187+00:00
-- url     : https://prove2.me/theorems/40aefc60-0c0a-4532-a171-94fe211ba08c
-- title:
--   OAI.Kadison.exists_countable_strong_contraction_tests: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_countable_strong_contraction_tests (P : VonNeumannAlgebra H) :
--       ∃ test : ℕ → H →L[ℂ] H,(∀ n,test n∈P ∧ ‖test n‖≤1) ∧
--         ∀ A : H →L[ℂ] H,A∈P → ‖A‖≤1 →
--           ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) ξ) atTop (𝓝 (A ξ))
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.exists_separable_cstar_bicommutant` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem exists_countable_strong_contraction_tests (P : VonNeumannAlgebra H) :
    ∃ test : ℕ → H →L[ℂ] H,(∀ n,test n∈P ∧ ‖test n‖≤1) ∧
      ∀ A : H →L[ℂ] H,A∈P → ‖A‖≤1 →
        ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) ξ) atTop (𝓝 (A ξ)) := by
  sorry

end Kadison

end

end
end

end OAI
end
