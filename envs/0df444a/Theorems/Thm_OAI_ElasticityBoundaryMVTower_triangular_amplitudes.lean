-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryMVTower_triangular_amplitudes
-- name    : OAI.ElasticityBoundaryMVTower.triangular_amplitudes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:20:57.410979+00:00
-- url     : https://prove2.me/theorems/9a4371ef-dd5b-492d-9631-0a78e0edb04d
-- title:
--   OAI.ElasticityBoundaryMVTower.triangular_amplitudes: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryMVTower.triangular_amplitudes` of [lean/OAI/MathematicalPhysics/Elasticity/BoundarySymbols.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundarySymbols.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryMVTower`, with `open scoped BigOperators`, `open ElasticityBoundaryMVNormal`):
--
--   ```lean
--   theorem triangular_amplitudes (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
--       (A : ℕ → (W →ₗ[ℂ] W)) (hA : A 0=normal l m)
--       (p₀ : W) (h₀ : normal l m p₀=0) :
--       ∃ p : ℕ → W, p 0=p₀ ∧
--         (∀ n, 0<n → boundary (p n)=0) ∧
--         ∀ n, ∑ k ∈ Finset.range (n+1), A k (p (n-k))=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryMVNormal.boundary` and `OAI.ElasticityBoundaryMVNormal.normal` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityBoundaryActualTower.finite_tensor_amplitude` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundarySymbols.lean (declaration OAI.ElasticityBoundaryMVTower.triangular_amplitudes)

import Mathlib
import Definitions.Def_OAIQ6El001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryMVTower
open ElasticityBoundaryMVNormal

theorem triangular_amplitudes (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (A : ℕ → (W →ₗ[ℂ] W)) (hA : A 0=normal l m)
    (p₀ : W) (h₀ : normal l m p₀=0) :
    ∃ p : ℕ → W, p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      ∀ n, ∑ k ∈ Finset.range (n+1), A k (p (n-k))=0 := by
  sorry

end ElasticityBoundaryMVTower

end
end

end OAI
end
