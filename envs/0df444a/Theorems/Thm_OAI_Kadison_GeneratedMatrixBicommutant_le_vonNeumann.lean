-- Prove2me | Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_le_vonNeumann
-- name    : OAI.Kadison.GeneratedMatrixBicommutant.le_vonNeumann
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:35:21.988773+00:00
-- url     : https://prove2.me/theorems/1f02a61c-590e-4b0b-ad1d-830a7dacfb09
-- title:
--   OAI.Kadison.GeneratedMatrixBicommutant.le_vonNeumann: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.GeneratedMatrixBicommutant`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma le_vonNeumann (N : VonNeumannAlgebra H)
--       (hstage : ∀ n a,φ (stage n a)∈N) : algebra size stage φ≤N
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.GeneratedMatrixBicommutant.algebra` (definitions bundle `OAIQ039C011` of this split).
--
--   **Used by.** The proof of `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` of this split imports it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ039C011

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

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison.GeneratedMatrixBicommutant

variable {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra A]

variable (size : ℕ → ℕ)

variable (stage : ∀ n,Matrix (Fin (size n+1)) (Fin (size n+1)) ℂ →⋆ₐ[ℂ] A)

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma le_vonNeumann (N : VonNeumannAlgebra H)
    (hstage : ∀ n a,φ (stage n a)∈N) : algebra size stage φ≤N := by
  sorry

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end
