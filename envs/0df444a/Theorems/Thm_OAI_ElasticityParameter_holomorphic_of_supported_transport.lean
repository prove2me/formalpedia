-- Prove2me | Theorems.Thm_OAI_ElasticityParameter_holomorphic_of_supported_transport
-- name    : OAI.ElasticityParameter.holomorphic_of_supported_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:29:54.084283+00:00
-- url     : https://prove2.me/theorems/3ae93507-f692-4ccd-929c-e3d7e603b863
-- title:
--   OAI.ElasticityParameter.holomorphic_of_supported_transport: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityParameter.holomorphic_of_supported_transport` of [lean/OAI/MathematicalPhysics/Elasticity/Transport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityParameter`, with `open Set`, `open scoped BigOperators`):
--
--   ```lean
--   theorem holomorphic_of_supported_transport
--       (e : k → E) (θ : k → Smooth (E × ℂ))
--       (hθx : ∀ r x z, (θ r : E × ℂ → ℂ) (x,z)=(θ r : E × ℂ → ℂ) (0,z))
--       (hθ : ∀ r x, Differentiable ℂ (fun z => (θ r : E × ℂ → ℂ) (x,z)))
--       (hplane : ∀ z, Function.Injective (characteristicPlane e (fun r => (θ r : E × ℂ → ℂ) (0,z))))
--       (a : n → n → Smooth (E × ℂ))
--       (ha : ∀ i j x, Differentiable ℂ (fun z => (a i j : E × ℂ → ℂ) (x,z)))
--       (u : n → Smooth (E × ℂ))
--       (he : ∀ i, ∑ r, θ r*delta (e r,0) (u i)=∑ j, a i j*u j)
--       {S : Set E} (hS : IsCompact S) (c : n → ℂ)
--       (hs : ∀ i x, x∉S → ∀ z, (u i : E × ℂ → ℂ) (x,z)=c i) :
--       ∀ i x, Differentiable ℂ (fun z => (u i : E × ℂ → ℂ) (x,z))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityParameter.Smooth`, `OAI.ElasticityParameter.characteristicPlane` and `OAI.ElasticityParameter.delta` (definitions bundle `OAIQ6El003` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityAugmented.supported_matrix_holomorphic` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transport.lean (declaration OAI.ElasticityParameter.holomorphic_of_supported_transport)

import Mathlib
import Definitions.Def_OAIQ6El003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityParameter
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

theorem holomorphic_of_supported_transport
    (e : k → E) (θ : k → Smooth (E × ℂ))
    (hθx : ∀ r x z, (θ r : E × ℂ → ℂ) (x,z)=(θ r : E × ℂ → ℂ) (0,z))
    (hθ : ∀ r x, Differentiable ℂ (fun z => (θ r : E × ℂ → ℂ) (x,z)))
    (hplane : ∀ z, Function.Injective (characteristicPlane e (fun r => (θ r : E × ℂ → ℂ) (0,z))))
    (a : n → n → Smooth (E × ℂ))
    (ha : ∀ i j x, Differentiable ℂ (fun z => (a i j : E × ℂ → ℂ) (x,z)))
    (u : n → Smooth (E × ℂ))
    (he : ∀ i, ∑ r, θ r*delta (e r,0) (u i)=∑ j, a i j*u j)
    {S : Set E} (hS : IsCompact S) (c : n → ℂ)
    (hs : ∀ i x, x∉S → ∀ z, (u i : E × ℂ → ℂ) (x,z)=c i) :
    ∀ i x, Differentiable ℂ (fun z => (u i : E × ℂ → ℂ) (x,z)) := by
  sorry
end ElasticityParameter

end

end OAI
end
