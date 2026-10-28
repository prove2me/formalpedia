-- Prove2me | Theorems.Thm_OAI_Kadison_GeneratedFreePair_original_generation
-- name    : OAI.Kadison.GeneratedFreePair.original_generation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T07:06:13.910687+00:00
-- url     : https://prove2.me/theorems/d1a39f3b-f105-4af3-9b71-e2e5bc537961
-- title:
--   OAI.Kadison.GeneratedFreePair.original_generation: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.GeneratedFreePair`, with `open scoped ComplexOrder InnerProductSpace`, `open FreeMoments`):
--
--   ```lean
--   lemma original_generation (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer
--       (Set.centralizer (((iSup (factors D k)).map (algebra D k).toStarSubalgebra.subtype) : Set _))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.GeneratedFreePair.algebra` (definitions bundle `OAIQ039C011` of this split); `OAI.Kadison.VonNeumannCStar.cstarAlgebra` (definitions bundle `OAIQ039C022` of this split); `OAI.Kadison.GeneratedFreePair.factors` (definitions bundle `OAIQ039C060` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.generated_free_small_corners_bound` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C060

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.GeneratedFreePair

open FreeMoments

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (D : VonNeumannAlgebra H) (k : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma original_generation (a : algebra D k) : (a:H →L[ℂ] H)∈Set.centralizer
    (Set.centralizer (((iSup (factors D k)).map (algebra D k).toStarSubalgebra.subtype) : Set _)) := by
  sorry

end Kadison.GeneratedFreePair

end

end
end

end OAI
end
