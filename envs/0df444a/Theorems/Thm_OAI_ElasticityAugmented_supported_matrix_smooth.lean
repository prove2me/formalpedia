-- Prove2me | Theorems.Thm_OAI_ElasticityAugmented_supported_matrix_smooth
-- name    : OAI.ElasticityAugmented.supported_matrix_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:34:32.401241+00:00
-- url     : https://prove2.me/theorems/4c5fbcf3-7ac4-41cc-9e06-9701fc4e12a6
-- title:
--   OAI.ElasticityAugmented.supported_matrix_smooth: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityAugmented.supported_matrix_smooth` of [lean/OAI/MathematicalPhysics/Elasticity/Holomorphy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Holomorphy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityAugmented`, with `open Set`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem supported_matrix_smooth (θ : Fin 3 → ℂ → ℂ)
--       (hθ : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i))
--       (hnull : ∀ z,∑ i,θ i z*θ i z=0) (hne : ∀ z,(fun i => θ i z)≠0)
--       (M₀ M₁ G : ℂ → Matrix n n Smooth)
--       (hM₀ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₀ q.2 i j : X → ℂ) q.1))
--       (hM₁ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₁ q.2 i j : X → ℂ) q.1))
--       {S : Set X} (hS : IsCompact S) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
--       (hχ1 : ∀ x∈S,(χ : X → ℂ) x=1)
--       (hs : ∀ z i j,tsupport ((G z i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆S)
--       (hMe : ∀ z x,x∉S → matrixEval x (M₀ z)=matrixEval x (M₁ z))
--       (he : ∀ z,matrixD (fun i => θ i z) (G z)=M₁ z*G z-G z*M₀ z) :
--       ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (G q.2 i j : X → ℂ) q.1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth` and `OAI.ElasticityAugmented.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.matrixD` and `OAI.ElasticityAugmented.matrixEval` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityAugmented.supported_matrix_holomorphic` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Holomorphy.lean (declaration OAI.ElasticityAugmented.supported_matrix_smooth)

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

theorem supported_matrix_smooth (θ : Fin 3 → ℂ → ℂ)
    (hθ : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i))
    (hnull : ∀ z,∑ i,θ i z*θ i z=0) (hne : ∀ z,(fun i => θ i z)≠0)
    (M₀ M₁ G : ℂ → Matrix n n Smooth)
    (hM₀ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₀ q.2 i j : X → ℂ) q.1))
    (hM₁ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₁ q.2 i j : X → ℂ) q.1))
    {S : Set X} (hS : IsCompact S) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈S,(χ : X → ℂ) x=1)
    (hs : ∀ z i j,tsupport ((G z i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆S)
    (hMe : ∀ z x,x∉S → matrixEval x (M₀ z)=matrixEval x (M₁ z))
    (he : ∀ z,matrixD (fun i => θ i z) (G z)=M₁ z*G z-G z*M₀ z) :
    ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (G q.2 i j : X → ℂ) q.1) := by
  sorry
end ElasticityAugmented

end
end

end OAI
end
