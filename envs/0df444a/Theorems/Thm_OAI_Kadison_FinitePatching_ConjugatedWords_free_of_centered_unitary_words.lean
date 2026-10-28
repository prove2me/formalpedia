-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_ConjugatedWords_free_of_centered_unitary_words
-- name    : OAI.Kadison.FinitePatching.ConjugatedWords.free_of_centered_unitary_words
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:52:57.342965+00:00
-- url     : https://prove2.me/theorems/4c1c53d6-5311-46fb-ba1e-c8d4e4f2e66a
-- title:
--   OAI.Kadison.FinitePatching.ConjugatedWords.free_of_centered_unitary_words: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching.ConjugatedWords`, with `open scoped ComplexOrder`, `open Words`):
--
--   ```lean
--   theorem free_of_centered_unitary_words (τ : A →ₗ[ℂ] ℂ)
--       (hu : (u:B)∈S) (hφ : ∀ a,φ a∈S)
--       (hρ : ∀ a∈S,∀ b∈S,ρ (a*b)=ρ (b*a))
--       (htrace : ∀ a,ρ (φ a)=τ a)
--       (hword : ∀ (J : Type) (x : J → A),(∀ j,τ (x j)=0) →
--         ∀ l : List (Letter J Bool),l≠[] → Valid l →
--           ρ (word (φ ∘ x) signPower (PartialUnitary.ofUnitary u) l)=0) :
--       FreeMoments.Free (pair φ u) ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FinitePatching.ConjugatedWords.pair` and `OAI.Kadison.FinitePatching.ConjugatedWords.signPower` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.FinitePatching.Words.Letter` and `OAI.Kadison.FinitePatching.Words.Valid` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.ofUnitary` and `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.sequenceUnitary_free` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C035

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

open scoped ComplexOrder

namespace Kadison.FinitePatching.ConjugatedWords

open Words

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (φ : A →⋆ₐ[ℂ] B) (u : unitary B)

variable (S : StarSubalgebra ℂ B) (ρ : B →ₗ[ℂ] ℂ)

omit [PartialOrder B] [StarOrderedRing B] in
include S in
theorem free_of_centered_unitary_words (τ : A →ₗ[ℂ] ℂ)
    (hu : (u:B)∈S) (hφ : ∀ a,φ a∈S)
    (hρ : ∀ a∈S,∀ b∈S,ρ (a*b)=ρ (b*a))
    (htrace : ∀ a,ρ (φ a)=τ a)
    (hword : ∀ (J : Type) (x : J → A),(∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        ρ (word (φ ∘ x) signPower (PartialUnitary.ofUnitary u) l)=0) :
    FreeMoments.Free (pair φ u) ρ := by
  sorry

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
end
