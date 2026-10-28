-- Prove2me | Theorems.Thm_OAI_Elasticity_dn_conic_comparison
-- name    : OAI.Elasticity.dn_conic_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:31:10.771994+00:00
-- url     : https://prove2.me/theorems/056419b0-6109-4074-8496-759a69a9677e
-- title:
--   OAI.Elasticity.dn_conic_comparison: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Elasticity.dn_conic_comparison` of [lean/OAI/MathematicalPhysics/Elasticity/Conic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Conic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Elasticity`, with `open Set`, `open scoped BigOperators Matrix`, `open ElasticityAugmented ElasticityCGO ElasticityConic`, `open ElasticityCoeffBounds (ExteriorConstant)`):
--
--   ```lean
--   theorem dn_conic_comparison {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
--       (r₀ : ℝ) (hr₀ : 1 ≤ r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
--       (lam m : Fin 2 → X → ℝ)
--       (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
--       (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
--       (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
--       (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
--       (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
--       (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) (b : Bool) (z : ℂ) :
--       let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
--       let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
--       let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
--       ∀ hk : ∀ q x,(k q : X → ℂ) x≠0,
--       ∀ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
--       let M := fun q => chartMatrix b z (transportT (chartTheta b z) (k q) (r q) (hk q) (hL q))
--         (transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hL q))
--       ∃ G : Matrix (Fin 3) (Fin 3) Smooth,
--         (∀ i j,tsupport ((G i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆closure Ω) ∧
--         matrixD (chartTheta b z) G=M 1*G-G*M 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth` and `OAI.ElasticityAugmented.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityConic.chartTheta` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityAugmented.matrixD`, `OAI.ElasticityAugmented.positiveRoot`, `OAI.ElasticityAugmented.positiveRoot_nonzero`, `OAI.ElasticityAugmented.smoothOfReal`, `OAI.ElasticityAugmented.transportQ`, `OAI.ElasticityAugmented.transportT`, `OAI.ElasticityCoeffBounds.ExteriorConstant` and `OAI.ElasticityConic.chartMatrix` (definitions bundle `OAIQ6El004` of this split); `OAI.Elasticity.BoundaryData`, `OAI.Elasticity.DN` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_global_coefficients_equal` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Conic.lean (declaration OAI.Elasticity.dn_conic_comparison)

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

theorem dn_conic_comparison {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1 ≤ r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) (b : Bool) (z : ℂ) :
    let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
    let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
    let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
    ∀ hk : ∀ q x,(k q : X → ℂ) x≠0,
    ∀ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
    let M := fun q => chartMatrix b z (transportT (chartTheta b z) (k q) (r q) (hk q) (hL q))
      (transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hL q))
    ∃ G : Matrix (Fin 3) (Fin 3) Smooth,
      (∀ i j,tsupport ((G i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆closure Ω) ∧
      matrixD (chartTheta b z) G=M 1*G-G*M 0 := by
  sorry
end Elasticity

end
end

end OAI
end
