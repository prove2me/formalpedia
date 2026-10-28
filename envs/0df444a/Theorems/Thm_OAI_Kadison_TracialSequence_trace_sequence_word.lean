-- Prove2me | Theorems.Thm_OAI_Kadison_TracialSequence_trace_sequence_word
-- name    : OAI.Kadison.TracialSequence.trace_sequence_word
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T09:58:51.235631+00:00
-- url     : https://prove2.me/theorems/f7d9db10-9885-4e09-b48a-df6e7e34af0b
-- title:
--   OAI.Kadison.TracialSequence.trace_sequence_word: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.TracialSequence`, with `open scoped ComplexOrder Topology BoundedContinuousFunction`, `open Filter`, `open FinitePatching FinitePatching.Words`):
--
--   ```lean
--   lemma trace_sequence_word {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
--       (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
--       {J K : Type*} (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
--       (x : J → A) (k : K → ℤ) (l : List (Letter J K))
--       (hlim : Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
--       sequenceTrace τ ω (word (((leftRestricted τ ω).comp constantSequence) ∘ x) k
--         (PartialUnitary.ofUnitary
--           (by exact sequenceUnitary τ ω u)) l)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.HilbertSequence.Pre` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.TracialSequence.constantSequence` (definitions bundle `OAIQ039C018` of this split); `OAI.Kadison.FinitePatching.Words.Letter` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.HilbertSequence.instAddCommGroupPre` and `OAI.Kadison.HilbertSequence.instModuleComplexPre` (definitions bundle `OAIQ039C026` of this split); `OAI.Kadison.FinitePatching.PartialUnitary.ofUnitary` and `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split); `OAI.Kadison.HilbertSequence.Space`, `OAI.Kadison.HilbertSequence.instInnerProductSpaceComplexPre` and `OAI.Kadison.HilbertSequence.instSeminormedAddCommGroupPre` (definitions bundle `OAIQ039C037` of this split); `OAI.Kadison.TracialSequence.boundedSubspace`, `OAI.Kadison.TracialSequence.instCompleteSpaceSubtypeSpaceGNSMemSubmoduleComplexBoundedSubspace` and `OAI.Kadison.TracialSequence.leftRestricted` (definitions bundle `OAIQ039C064` of this split); `OAI.Kadison.TracialSequence.sequenceTrace` and `OAI.Kadison.TracialSequence.sequenceUnitary` (definitions bundle `OAIQ039C069` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.sequenceUnitary_free` of this split imports it.
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

open FinitePatching FinitePatching.Words

variable {A : Type} [CStarAlgebra A]

lemma trace_sequence_word {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    {J K : Type*} (hω : (ω : Filter ℕ)≤atTop) (u : ℕ → unitary A)
    (x : J → A) (k : K → ℤ) (l : List (Letter J K))
    (hlim : Tendsto (fun n => τ (word x k (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    sequenceTrace τ ω (word (((leftRestricted τ ω).comp constantSequence) ∘ x) k
      (PartialUnitary.ofUnitary
        (by exact sequenceUnitary τ ω u)) l)=0 := by
  sorry

end Kadison.TracialSequence

end

end OAI
end
