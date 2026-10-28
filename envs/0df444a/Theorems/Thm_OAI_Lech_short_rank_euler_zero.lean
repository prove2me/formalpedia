-- Prove2me | Theorems.Thm_OAI_Lech_short_rank_euler_zero
-- name    : OAI.Lech.short_rank_euler_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:20:38.87702+00:00
-- url     : https://prove2.me/theorems/057379b5-a109-4415-b392-18f51ddedb3c
-- title:
--   OAI.Lech.short_rank_euler_zero: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   lemma short_rank_euler_zero (hd : 0 < dimension R)
--       (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
--       ∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
--         (Module.finrank R (F.X (-(i:ℤ))):ℝ) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.CharP.dutta_minimal_estimate` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

lemma short_rank_euler_zero (hd : 0 < dimension R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    ∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
      (Module.finrank R (F.X (-(i:ℤ))):ℝ) = 0 := by
  sorry
end Lech

end

end OAI
end
