-- Prove2me | Theorems.Thm_OAI_Elasticity_dn_global_coefficients_equal
-- name    : OAI.Elasticity.dn_global_coefficients_equal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:31:17.801707+00:00
-- url     : https://prove2.me/theorems/f698d3a6-ff8c-4e2a-a3f7-595a57d491ab
-- title:
--   OAI.Elasticity.dn_global_coefficients_equal: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Elasticity.dn_global_coefficients_equal` of [lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Elasticity`, with `open Set`, `open scoped BigOperators Matrix`, `open ElasticityAugmented ElasticityCGO ElasticityConic`, `open ElasticityCoeffBounds (ExteriorConstant)`):
--
--   ```lean
--   theorem dn_global_coefficients_equal {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
--       (lam m : Fin 2 → X → ℝ)
--       (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
--       (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
--       (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
--       (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
--       (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
--       (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
--       lam 0=lam 1 ∧ m 0=m 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.smoothOfReal` and `OAI.ElasticityCoeffBounds.ExteriorConstant` (definitions bundle `OAIQ6El004` of this split); `OAI.Elasticity.BoundaryData`, `OAI.Elasticity.DN` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proof of `OAI.Elasticity.global_uniqueness` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean (declaration OAI.Elasticity.dn_global_coefficients_equal)

import Mathlib
import Definitions.Def_ElasticityUniqueness
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
namespace Elasticity
open ElasticityAugmented ElasticityCGO ElasticityConic
open ElasticityCoeffBounds (ExteriorConstant)

theorem dn_global_coefficients_equal {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    lam 0=lam 1 ∧ m 0=m 1 := by
  sorry
end Elasticity

end
end

end OAI
end
