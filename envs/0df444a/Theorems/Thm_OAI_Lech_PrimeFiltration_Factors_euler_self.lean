-- Prove2me | Theorems.Thm_OAI_Lech_PrimeFiltration_Factors_euler_self
-- name    : OAI.Lech.PrimeFiltration.Factors.euler_self
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:25:21.640978+00:00
-- url     : https://prove2.me/theorems/c53046d1-a05b-42a2-862c-4274a5912a32
-- title:
--   OAI.Lech.PrimeFiltration.Factors.euler_self: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech.PrimeFiltration`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex`):
--
--   ```lean
--   lemma Factors.euler_self {ps : List (Ideal R)} (h : Factors (⊥ : Submodule R R) ps)
--       (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
--       shortEuler R F=
--         (ps.map (fun P => shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))))).sum
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.PrimeFiltration.Factors` (definitions bundle `OAIQ032L006` of this split); `OAI.Lech.tensorModuleFunctor` (definitions bundle `OAIQ032L018` of this split); `OAI.Lech.shortEuler` (the published bundle `Def_DuttaDomain`).
--
--   **Used by.** The proof of `OAI.Lech.dutta_algClosed` of this split imports it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L018

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
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

namespace PrimeFiltration
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

lemma Factors.euler_self {ps : List (Ideal R)} (h : Factors (⊥ : Submodule R R) ps)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    shortEuler R F=
      (ps.map (fun P => shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))))).sum := by
  sorry
end PrimeFiltration
end Lech

end

end OAI
end
