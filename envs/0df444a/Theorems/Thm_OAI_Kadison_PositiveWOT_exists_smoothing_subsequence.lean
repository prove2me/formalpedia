-- Prove2me | Theorems.Thm_OAI_Kadison_PositiveWOT_exists_smoothing_subsequence
-- name    : OAI.Kadison.PositiveWOT.exists_smoothing_subsequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:30:20.409797+00:00
-- url     : https://prove2.me/theorems/0c046705-40ca-4058-af82-036bb516c955
-- title:
--   OAI.Kadison.PositiveWOT.exists_smoothing_subsequence: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.PositiveWOT`, with `open Filter Finset`, `open scoped ComplexOrder InnerProductSpace Topology`):
--
--   ```lean
--   theorem exists_smoothing_subsequence [TopologicalSpace.SeparableSpace H]
--       (M : VonNeumannAlgebra H) (A : ℕ → H →L[ℂ] H) (hAM : ∀ n,A n∈M)
--       (hA : ∀ n,0≤A n) (ht : ∀ x,Tendsto (fun n => A n x) atTop (𝓝 0)) :
--       ∃ u : ℕ → ℕ,StrictMono u ∧ ∃ B : H →L[ℂ] H,
--         B∈M ∧ 0≤B ∧ B≤1 ∧ Function.Injective B ∧
--         ∀ k,‖B*A (u k)*B‖≤1/((k:ℝ)+1)
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.PositiveWOT.positive_strong_null` of this split imports it.
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

open Filter Finset

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_smoothing_subsequence [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (A : ℕ → H →L[ℂ] H) (hAM : ∀ n,A n∈M)
    (hA : ∀ n,0≤A n) (ht : ∀ x,Tendsto (fun n => A n x) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ,StrictMono u ∧ ∃ B : H →L[ℂ] H,
      B∈M ∧ 0≤B ∧ B≤1 ∧ Function.Injective B ∧
      ∀ k,‖B*A (u k)*B‖≤1/((k:ℝ)+1) := by
  sorry

end Kadison.PositiveWOT

end

end
end

end OAI
end
