-- Prove2me | Theorems.Thm_OAI_Kadison_FinitePatching_Words_moment_limit_of_contractions
-- name    : OAI.Kadison.FinitePatching.Words.moment_limit_of_contractions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:53:10.215165+00:00
-- url     : https://prove2.me/theorems/f6acb74a-b67b-4f0b-b551-2e758e745520
-- title:
--   OAI.Kadison.FinitePatching.Words.moment_limit_of_contractions: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FinitePatching.Words`, with `open scoped ComplexOrder Topology`, `open Filter`):
--
--   ```lean
--   lemma moment_limit_of_contractions (τ : A →ₚ[ℂ] ℂ) (k : K → ℤ) (v : ℕ → PartialUnitary A)
--       (hlim : ∀ x : J → A,(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
--         ∀ l : List (Letter J K),l≠[] → Valid l →
--           Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0))
--       (x : J → A) (hx : ∀ j,τ (x j)=0)
--       (l : List (Letter J K)) (hl : l≠[]) (hv : Valid l) :
--       Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FinitePatching.PartialUnitary` (definitions bundle `OAIQ039C009` of this split); `OAI.Kadison.FinitePatching.Words.Letter` and `OAI.Kadison.FinitePatching.Words.Valid` (definitions bundle `OAIQ039C025` of this split); `OAI.Kadison.FinitePatching.Words.word` (definitions bundle `OAIQ039C035` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.sequenceUnitary_free` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C035

section

attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching.Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in
lemma moment_limit_of_contractions (τ : A →ₚ[ℂ] ℂ) (k : K → ℤ) (v : ℕ → PartialUnitary A)
    (hlim : ∀ x : J → A,(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J K),l≠[] → Valid l →
        Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0))
    (x : J → A) (hx : ∀ j,τ (x j)=0)
    (l : List (Letter J K)) (hl : l≠[]) (hv : Valid l) :
    Tendsto (fun n => τ (word x k (v n) l)) atTop (𝓝 0) := by
  sorry

end Kadison.FinitePatching.Words

end

end
end

end OAI
end
