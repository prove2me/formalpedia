-- Prove2me | Theorems.Thm_OAI_ElasticityAugmented_supported_matrix_unique
-- name    : OAI.ElasticityAugmented.supported_matrix_unique
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:34:38.730192+00:00
-- url     : https://prove2.me/theorems/4dcd74bd-5458-4e36-946a-ed1a57321543
-- title:
--   OAI.ElasticityAugmented.supported_matrix_unique: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityAugmented.supported_matrix_unique` of [lean/OAI/MathematicalPhysics/Elasticity/Conic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Conic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityAugmented`, with `open Set`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem supported_matrix_unique (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
--       (M₀ M₁ G H : Matrix n n Smooth)
--       (heG : matrixD θ G=M₁*G-G*M₀) (heH : matrixD θ H=M₁*H-H*M₀)
--       (hc : ∀ i j,HasCompactSupport ((G i j-H i j : Smooth) : X → ℂ)) : G=H
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth` and `OAI.ElasticityAugmented.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.matrixD` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityConic.physical_conic_connections_equal` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Conic.lean (declaration OAI.ElasticityAugmented.supported_matrix_unique)

import Mathlib
import Definitions.Def_OAIQ6El004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem supported_matrix_unique (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (M₀ M₁ G H : Matrix n n Smooth)
    (heG : matrixD θ G=M₁*G-G*M₀) (heH : matrixD θ H=M₁*H-H*M₀)
    (hc : ∀ i j,HasCompactSupport ((G i j-H i j : Smooth) : X → ℂ)) : G=H := by
  sorry
end ElasticityAugmented

end
end

end OAI
end
