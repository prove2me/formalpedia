-- Prove2me | Theorems.Thm_OAI_Kadison_commutatorSeminorm_nonneg
-- name    : OAI.Kadison.commutatorSeminorm_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:31:10.10077+00:00
-- url     : https://prove2.me/theorems/e7ce384e-edde-4f19-afad-3d127593310d
-- title:
--   OAI.Kadison.commutatorSeminorm_nonneg: intermediate lemma from OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Kadison`, with `open scoped InnerProductSpace BigOperators ComplexOrder`):
--
--   ```lean
--   lemma commutatorSeminorm_nonneg (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
--       0 ≤ commutatorSeminorm P Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Kadison.commutatorSeminorm` (the published bundle `Def_UniformCommutator`).
--
--   **Used by.** The proofs of `OAI.Kadison.CentralAverage.exists_center_average`, `OAI.Kadison.CentralSpectral.separable_uniform_bound`, `OAI.Kadison.CentralSpectral.stable_model_bound`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields`, `OAI.Kadison.MatrixTower.finite_standard_gauge_bound`, `OAI.Kadison.NormalRepresentation.finite_standard_compression_bound`, `OAI.Kadison.NormalRepresentation.separable_traced_factor_bound`, `OAI.Kadison.SeparableTest.bound_of_separable_bound`, `OAI.Kadison.SeparableTest.seminorm_bound`, `OAI.Kadison.commutator_column_bound`, `OAI.Kadison.uniform_commutator_atomic_factor`, `OAI.Kadison.uniform_commutator_finiteDimensional`, `OAI.Kadison.uniform_commutator_of_isometries` and `OAI.Kadison.uniform_commutator_separable_factor` of this split import it.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_UniformCommutator

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma commutatorSeminorm_nonneg (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    0 ≤ commutatorSeminorm P Y := by
  sorry

end Kadison

end

end
end

end OAI
end
