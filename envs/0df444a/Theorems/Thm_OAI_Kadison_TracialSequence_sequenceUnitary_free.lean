-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_sequenceUnitary_free
-- name    : OAI.Kadison.TracialSequence.sequenceUnitary_free
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:57:48.652909+00:00
-- url     : https://prove2.me/theorems/4de4a228-014f-408e-b540-fa577c7bc618
-- title:
--   OAI.Kadison.TracialSequence.sequenceUnitary_free: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped ComplexOrder Topology BoundedContinuousFunction`, `open Filter`, `open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords`):
--
--   ```lean
--   lemma sequenceUnitary_free (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
--       (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
--       (hlim : ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
--         ∀ l : List (Letter J Bool),l≠[] → Valid l →
--           Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
--       FreeMoments.Free (pair (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
--         ((leftRestricted τ ω).comp constantSequence) (sequenceUnitary τ ω u))
--         (sequenceTrace τ ω).toLinearMap
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FinitePatching.ConjugatedWords.pair` and `OAI.Kadison.FinitePatching.ConjugatedWords.signPower` (definitions bundle `OAIQ039C010` of this split); `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.constantSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.FinitePatching.Words.Letter` and `OAI.Kadison.FinitePatching.Words.Valid` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.ofUnitary` and `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.TracialSequence.sequenceTrace` and `OAI.Kadison.TracialSequence.sequenceUnitary` (definitions bundle `OAIQ039C069` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.exists_freeCornerPosition_of_equiv_tower` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C069

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

lemma sequenceUnitary_free (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
    (hlim : ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    FreeMoments.Free (pair (A := A) (B := boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)
      ((leftRestricted τ ω).comp constantSequence) (sequenceUnitary τ ω u))
      (sequenceTrace τ ω).toLinearMap := by
  sorry

end Kadison.TracialSequence

end

end OAI
end
