-- Prove2me | Theorems.Thm_OAI_Kadison_EquivariantBicommutant_bicommutant_range
-- name    : OAI.Kadison.EquivariantBicommutant.bicommutant_range
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:28:45.372557+00:00
-- url     : https://prove2.me/theorems/3f8c3989-24fd-4bd2-865a-f907ed31352a
-- title:
--   OAI.Kadison.EquivariantBicommutant.bicommutant_range: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.EquivariantBicommutant`):
--
--   ```lean
--   lemma bicommutant_range {C : Type*} (e : A ≃* B) (f : C → A)
--       (hf : Set.centralizer (Set.centralizer (Set.range f))=Set.range f) :
--       Set.centralizer (Set.centralizer (Set.range (e ∘ f)))=Set.range (e ∘ f)
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

namespace Kadison.EquivariantBicommutant

variable {A B : Type*} [Monoid A] [Monoid B]

lemma bicommutant_range {C : Type*} (e : A ≃* B) (f : C → A)
    (hf : Set.centralizer (Set.centralizer (Set.range f))=Set.range f) :
    Set.centralizer (Set.centralizer (Set.range (e ∘ f)))=Set.range (e ∘ f) := by
  sorry

end Kadison.EquivariantBicommutant

end

end
end

end OAI
end
