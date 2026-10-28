-- Prove2me | Theorems.Thm_OAI_Lech_frobenius_shortComplex_homology_finiteLength
-- name    : OAI.Lech.frobenius_shortComplex_homology_finiteLength
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:19:48.859742+00:00
-- url     : https://prove2.me/theorems/f157355d-b1aa-4b65-aea5-b25bd403cd78
-- title:
--   OAI.Lech.frobenius_shortComplex_homology_finiteLength: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`):
--
--   ```lean
--   theorem frobenius_shortComplex_homology_finiteLength
--       [IsLocalRing R] [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
--       (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) (n : ℕ) (i : ℤ) :
--       IsFiniteLength R ((frobeniusComplex R p n F).homology i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.frobeniusComplex` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proofs of `OAI.Lech.CharP.dutta_minimal_estimate`, `OAI.Lech.CharP.perfection_complex_value`, `OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer`, `OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound`, `OAI.Lech.dutta_algClosed`, `OAI.Lech.dutta_dimension_zero` and `OAI.Lech.dutta_domain` of this split import it.
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
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

theorem frobenius_shortComplex_homology_finiteLength
    [IsLocalRing R] [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) (n : ℕ) (i : ℤ) :
    IsFiniteLength R ((frobeniusComplex R p n F).homology i) := by
  sorry
end Lech

end

end OAI
end
