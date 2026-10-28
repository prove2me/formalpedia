-- Prove2me | Theorems.Thm_OAI_ElasticityBoundaryPacket_pair_separates
-- name    : OAI.ElasticityBoundaryPacket.pair_separates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:28:05.653167+00:00
-- url     : https://prove2.me/theorems/97348074-050c-4ae6-b8fb-b1a3ce03fe1b
-- title:
--   OAI.ElasticityBoundaryPacket.pair_separates: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityBoundaryPacket.pair_separates` of [lean/OAI/MathematicalPhysics/Elasticity/BoundaryValues.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryValues.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityBoundaryPacket`, with `open scoped Matrix BigOperators`, `open ElasticityBoundaryLeading ElasticityBoundaryWeights`):
--
--   ```lean
--   lemma pair_separates (n : ℕ) (l₁ m₁ l₂ m₂ D L M : ℂ)
--       (hm₁ : m₁≠0) (hm₂ : m₂≠0) (hp₁ : l₁+3*m₁≠0) (hp₂ : l₂+3*m₂≠0)
--       (hD : D≠0)
--       (h : ∀ p q : W, normal l₁ m₁ p=0 → normal l₂ m₂ q=0 →
--         frozenPair n (fun i α j β => D*elasticityTensor L M i α j β) p q=0) : L=0 ∧ M=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityBoundaryLayerOperator.elasticityTensor`, `OAI.ElasticityBoundaryMVCalculus.MP`, `OAI.ElasticityBoundaryMVNormal.W`, `OAI.ElasticityBoundaryMVNormal.normal`, `OAI.ElasticityBoundaryPacket.I` and `OAI.ElasticityBoundaryPacket.frozenPair` (definitions bundle `OAIQ6El001` of this split).
--
--   **Used by.** The proofs of `OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step` and `OAI.ElasticityBoundaryPacket.boundary_values_global` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/BoundaryValues.lean (declaration OAI.ElasticityBoundaryPacket.pair_separates)

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
open scoped Matrix BigOperators
namespace ElasticityBoundaryPacket
open ElasticityBoundaryLeading ElasticityBoundaryWeights
  ElasticityBoundarySymbol ElasticityBoundaryMVNormal ElasticityBoundaryParameter ElasticityBoundaryLayerOperator

lemma pair_separates (n : ℕ) (l₁ m₁ l₂ m₂ D L M : ℂ)
    (hm₁ : m₁≠0) (hm₂ : m₂≠0) (hp₁ : l₁+3*m₁≠0) (hp₂ : l₂+3*m₂≠0)
    (hD : D≠0)
    (h : ∀ p q : W, normal l₁ m₁ p=0 → normal l₂ m₂ q=0 →
      frozenPair n (fun i α j β => D*elasticityTensor L M i α j β) p q=0) : L=0 ∧ M=0 := by
  sorry

end ElasticityBoundaryPacket

end
end

end OAI
end
