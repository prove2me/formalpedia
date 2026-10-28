-- Prove2me | Theorems.Thm_OAI_Lech_finiteHomology_extendScalars
-- name    : OAI.Lech.finiteHomology_extendScalars
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:17:51.793224+00:00
-- url     : https://prove2.me/theorems/380bbf90-b5ae-4374-bc64-c81123afe9f9
-- title:
--   OAI.Lech.finiteHomology_extendScalars: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   lemma finiteHomology_extendScalars (φ : R →+* S)
--       (hd : dimension S = dimension R)
--       (hφ : ((IsLocalRing.maximalIdeal R).map φ).radical = IsLocalRing.maximalIdeal S)
--       (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
--       IsFiniteHomologyComplex S (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj F)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.extendScalars_additive` (definitions bundle `OAIQ032L004` of this split); `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.dimension` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proofs of `OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer`, `OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero`, `OAI.Lech.cyclicDuttaSequence_tendsto`, `OAI.Lech.dutta_algClosed` and `OAI.Lech.dutta_domain` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L004
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
variable {R S : Type u} [CommRing R] [CommRing S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]

lemma finiteHomology_extendScalars (φ : R →+* S)
    (hd : dimension S = dimension R)
    (hφ : ((IsLocalRing.maximalIdeal R).map φ).radical = IsLocalRing.maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    IsFiniteHomologyComplex S (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj F) := by
  sorry
end Lech

end

end OAI
end
