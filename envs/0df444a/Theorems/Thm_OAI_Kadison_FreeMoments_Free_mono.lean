-- Prove2me | Theorems.Thm_OAI_Kadison_FreeMoments_Free_mono
-- name    : OAI.Kadison.FreeMoments.Free.mono
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:34:51.503286+00:00
-- url     : https://prove2.me/theorems/e968cfa0-656f-4d30-804e-9c0363d99e7d
-- title:
--   OAI.Kadison.FreeMoments.Free.mono: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.FreeMoments`):
--
--   ```lean
--   lemma Free.mono (hfree : Free T τ) (hle : ∀ i,S i≤T i) : Free S τ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.FreeMoments.Free` (definitions bundle `OAIQ039C010` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A ι : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {S T : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

lemma Free.mono (hfree : Free T τ) (hle : ∀ i,S i≤T i) : Free S τ := by
  sorry

end Kadison.FreeMoments

end

end
end

end OAI
end
