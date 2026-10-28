-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_pullUnitary_moment_limits
-- name    : OAI.Kadison.TracialSequence.pullUnitary_moment_limits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:23:22.885977+00:00
-- url     : https://prove2.me/theorems/deaf7376-7115-40ee-9e33-7aa5aae151db
-- title:
--   OAI.Kadison.TracialSequence.pullUnitary_moment_limits: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped ComplexOrder Topology BoundedContinuousFunction`, `open Filter`, `open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords`):
--
--   ```lean
--   lemma pullUnitary_moment_limits (e : A ≃⋆ₐ[ℂ] B) (τ : A →ₚ[ℂ] ℂ) (σ : B →ₚ[ℂ] ℂ)
--       (htrace : ∀ a,σ (e a)=τ a) (u : ℕ → unitary B)
--       (hu : ∀ (J : Type) (x : J → B),(∀ j,‖x j‖≤1) → (∀ j,σ (x j)=0) →
--         ∀ l : List (Letter J Bool),l≠[] → Valid l →
--           Tendsto (fun n => σ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
--       ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
--         ∀ l : List (Letter J Bool),l≠[] → Valid l →
--           Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (pullUnitary e (u n))) l)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FinitePatching.ConjugatedWords.signPower` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.TracialSequence.pullUnitary` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.FinitePatching.Words.Letter` and `OAI.Kadison.FinitePatching.Words.Valid` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.ofUnitary` and `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C035

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma pullUnitary_moment_limits (e : A ≃⋆ₐ[ℂ] B) (τ : A →ₚ[ℂ] ℂ) (σ : B →ₚ[ℂ] ℂ)
    (htrace : ∀ a,σ (e a)=τ a) (u : ℕ → unitary B)
    (hu : ∀ (J : Type) (x : J → B),(∀ j,‖x j‖≤1) → (∀ j,σ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => σ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (pullUnitary e (u n))) l)) atTop (𝓝 0) := by
  sorry

end Kadison.TracialSequence

end

end
end

end OAI
end
