-- Prove2me | Theorems.Thm_OAI_Kadison_traceFaithfulHom_injective
-- name    : OAI.Kadison.traceFaithfulHom_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:24.472651+00:00
-- url     : https://prove2.me/theorems/8952ae6a-5061-48e2-9751-d33bb6e53670
-- title:
--   OAI.Kadison.traceFaithfulHom_injective: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`):
--
--   ```lean
--   lemma traceFaithfulHom_injective (φ : A →⋆ₐ[ℂ] B) (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
--       (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (htrace : ∀ a,ρ (φ a)=τ a) :
--       Function.Injective φ
--   ```
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` of this split imports it.
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

namespace Kadison

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

omit [StarModule ℂ A] [StarModule ℂ B] in
lemma traceFaithfulHom_injective (φ : A →⋆ₐ[ℂ] B) (τ : A →ₗ[ℂ] ℂ) (ρ : B →ₗ[ℂ] ℂ)
    (hfaith : ∀ a : A,τ (star a*a)=0 → a=0) (htrace : ∀ a,ρ (φ a)=τ a) :
    Function.Injective φ := by
  sorry

end Kadison

end

end
end

end OAI
end
