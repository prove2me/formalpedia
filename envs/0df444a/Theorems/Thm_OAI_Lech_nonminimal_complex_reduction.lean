-- Prove2me | Theorems.Thm_OAI_Lech_nonminimal_complex_reduction
-- name    : OAI.Lech.nonminimal_complex_reduction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:19:47.474293+00:00
-- url     : https://prove2.me/theorems/55694c58-8e5b-40a4-94c1-6253cc371ccf
-- title:
--   OAI.Lech.nonminimal_complex_reduction: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   lemma nonminimal_complex_reduction (F : CochainComplex (ModuleCat.{u} R) ℤ)
--       (hF : IsFiniteHomologyComplex R F) (hn : ¬ IsMinimalComplex F) :
--       ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
--         IsFiniteHomologyComplex R G ∧ Nonempty (HomotopyEquiv F G) ∧
--           complexRankSum G < complexRankSum F
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsFiniteHomologyComplex` and `OAI.Lech.IsMinimalComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.complexRankSum` (definitions bundle `OAIQ032L009` of this split).
--
--   **Used by.** The proof of `OAI.Lech.CharP.dutta_lower_bound_infinite_perfect` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L009

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
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
lemma nonminimal_complex_reduction (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (hn : ¬ IsMinimalComplex F) :
    ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
      IsFiniteHomologyComplex R G ∧ Nonempty (HomotopyEquiv F G) ∧
        complexRankSum G < complexRankSum F := by
  sorry
end Lech

end

end OAI
end
