-- Prove2me | Theorems.Thm_OAI_Lech_shortComplex_nullScalar_radical
-- name    : OAI.Lech.shortComplex_nullScalar_radical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:20:23.831896+00:00
-- url     : https://prove2.me/theorems/1b1bc2cc-999d-4710-8811-7bef4a3ce050
-- title:
--   OAI.Lech.shortComplex_nullScalar_radical: intermediate lemma from OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Lech`, with `open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex`):
--
--   ```lean
--   lemma shortComplex_nullScalar_radical [IsNoetherianRing R] [IsLocalRing R]
--       (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
--       IsLocalRing.maximalIdeal R ≤ (Koszul.nullScalarIdeal F).radical
--   ```
--
--   **Definitions.** The statement is written with `OAI.Lech.IsFiniteHomologyComplex` (definitions bundle `OAIQ032L005` of this split); `OAI.Lech.Koszul.nullScalarIdeal` (definitions bundle `OAIQ032L006` of this split).
--
--   **Used by.** The proofs of `OAI.Lech.CharP.dutta_minimal_estimate`, `OAI.Lech.PrimeFiltration.Factors.euler_self`, `OAI.Lech.SeparableOrder.normalizedLength_perfection_shortComplex_homology`, `OAI.Lech.finiteHomology_extendScalars` and `OAI.Lech.frobenius_quotient_homology_bound` of this split import it.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L006

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

lemma shortComplex_nullScalar_radical [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    IsLocalRing.maximalIdeal R ≤ (Koszul.nullScalarIdeal F).radical := by
  sorry

end Lech

end

end OAI
end
