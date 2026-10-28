-- Prove2me | Theorems.Thm_OAI_Kadison_AtomicFactor_Decomposition_finite_dimensional
-- name    : OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:54.161592+00:00
-- url     : https://prove2.me/theorems/a928b81c-d739-436d-8411-70e8684973a5
-- title:
--   OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.AtomicFactor.Decomposition`, with `open scoped ComplexOrder InnerProductSpace`):
--
--   ```lean
--   theorem finite_dimensional [Finite D.I] (hp : IsMinimalProjection M p) :
--       FiniteDimensional ℂ M
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.AtomicFactor.Decomposition` and `OAI.Kadison.AtomicFactor.IsMinimalProjection` (definitions bundle `OAIQ039C000` of this split); `OAI.Kadison.VonNeumannCStar.isClosed` and `OAI.Kadison.VonNeumannCStar.smulMemClass` (definitions bundle `OAIQ039C002` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.uniform_commutator_atomic_factor` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C000
import Definitions.Def_OAIQ039C002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.AtomicFactor.Decomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : Decomposition M p)

theorem finite_dimensional [Finite D.I] (hp : IsMinimalProjection M p) :
    FiniteDimensional ℂ M := by
  sorry

end Kadison.AtomicFactor.Decomposition

end

end
end

end OAI
end
