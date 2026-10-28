-- Prove2me | Theorems.Thm_OAI_Kadison_GeneratedMatrixBicommutant_in_range
-- name    : OAI.Kadison.GeneratedMatrixBicommutant.in_range
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:34:52.572876+00:00
-- url     : https://prove2.me/theorems/c61dfecf-360c-467f-b5bd-3495216a4ba4
-- title:
--   OAI.Kadison.GeneratedMatrixBicommutant.in_range: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison.GeneratedMatrixBicommutant`, with `open scoped ComplexOrder Matrix.Norms.L2Operator`):
--
--   ```lean
--   lemma in_range (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ)
--       (a : algebra size stage φ) : (a:H →L[ℂ] H)∈Set.range φ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.GeneratedMatrixBicommutant.algebra` (definitions bundle `OAIQ039C011` of this split).
--
--   **Used by.** The proofs of `OAI.Kadison.GeneratedMatrixBicommutant.factor` and `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract` of this split import it.
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

lemma in_range (hφ : Set.centralizer (Set.centralizer (Set.range φ))=Set.range φ)
    (a : algebra size stage φ) : (a:H →L[ℂ] H)∈Set.range φ := by
  sorry

end Kadison.GeneratedMatrixBicommutant

end

end
end

end OAI
end
