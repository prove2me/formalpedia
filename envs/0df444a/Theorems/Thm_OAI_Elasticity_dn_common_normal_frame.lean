-- Prove2me | Theorems.Thm_OAI_Elasticity_dn_common_normal_frame
-- name    : OAI.Elasticity.dn_common_normal_frame
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:31:09.488006+00:00
-- url     : https://prove2.me/theorems/b2da8f4e-14d6-4a6e-be11-49a46897bdbe
-- title:
--   OAI.Elasticity.dn_common_normal_frame: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Elasticity.dn_common_normal_frame` of [lean/OAI/MathematicalPhysics/Elasticity/CommonFrame.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CommonFrame.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Elasticity`, with `open Set`, `open scoped BigOperators`, `open ElasticityAugmented ElasticityCGO`, `open ElasticityCoeffBounds (ExteriorConstant)`):
--
--   ```lean
--   theorem dn_common_normal_frame {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
--       (r₀ : ℝ) (hr₀ : 1 ≤ r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
--       (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
--       (lam m : Fin 2 → X → ℝ)
--       (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
--       (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
--       (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
--       (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
--       (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
--       (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
--       let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
--       let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
--       let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
--       ∃ hk : ∀ q x,(k q : X → ℂ) x≠0,
--       ∃ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
--       ∃ p : Fin 2 → Fin 3 → Fin 3 → Smooth,∃ s : Fin 2 → Fin 3 → Smooth,
--       ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
--         (∀ q ν,normal θ (p q ν)=0) ∧
--         (∀ q ν x,x∈Metric.ball 0 (r₀+3) →
--           (∀ i,(direction (A := Smooth) coord θ (p q ν i) : X → ℂ) x=θ i*(s q ν : X → ℂ) x) ∧
--           (direction (A := Smooth) coord θ (s q ν) : X → ℂ) x=
--             ((transportT θ (k q) (r q) (hk q) (hL q)*s q ν+
--               ∑ i,transportQ θ (k q) (r q) (hr q) (hk q) (hL q) i*p q ν i : Smooth) : X → ℂ) x) ∧
--         (∀ ν x,x∉closure Ω → (∀ i,(p 0 ν i : X → ℂ) x=(p 1 ν i : X → ℂ) x) ∧
--           (s 0 ν : X → ℂ) x=(s 1 ν : X → ℂ) x) ∧
--         ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
--           ((fun i => (p 0 ν i : X → ℂ) x),(s 0 ν : X → ℂ) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.coord`, `OAI.ElasticityAugmented.direction` and `OAI.ElasticityAugmented.normal` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityFrame.Amp`, `OAI.ElasticityFrame.Fiber` and `OAI.ElasticityFrame.fiber` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityAugmented.positiveRoot`, `OAI.ElasticityAugmented.positiveRoot_nonzero`, `OAI.ElasticityAugmented.smoothOfReal`, `OAI.ElasticityAugmented.transportQ`, `OAI.ElasticityAugmented.transportT` and `OAI.ElasticityCoeffBounds.ExteriorConstant` (definitions bundle `OAIQ6El004` of this split); `OAI.Elasticity.BoundaryData`, `OAI.Elasticity.DN` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_conic_comparison` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CommonFrame.lean (declaration OAI.Elasticity.dn_common_normal_frame)

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
open scoped BigOperators
namespace Elasticity
open ElasticityAugmented ElasticityCGO
open ElasticityCoeffBounds (ExteriorConstant)

theorem dn_common_normal_frame {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (r₀ : ℝ) (hr₀ : 1 ≤ r₀) (hK : closure Ω⊆Metric.closedBall 0 r₀)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
    let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
    let hr := fun q => positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1)
    ∃ hk : ∀ q x,(k q : X → ℂ) x≠0,
    ∃ hL : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0,
    ∃ p : Fin 2 → Fin 3 → Fin 3 → Smooth,∃ s : Fin 2 → Fin 3 → Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ q ν,normal θ (p q ν)=0) ∧
      (∀ q ν x,x∈Metric.ball 0 (r₀+3) →
        (∀ i,(direction (A := Smooth) coord θ (p q ν i) : X → ℂ) x=θ i*(s q ν : X → ℂ) x) ∧
        (direction (A := Smooth) coord θ (s q ν) : X → ℂ) x=
          ((transportT θ (k q) (r q) (hk q) (hL q)*s q ν+
            ∑ i,transportQ θ (k q) (r q) (hr q) (hk q) (hL q) i*p q ν i : Smooth) : X → ℂ) x) ∧
      (∀ ν x,x∉closure Ω → (∀ i,(p 0 ν i : X → ℂ) x=(p 1 ν i : X → ℂ) x) ∧
        (s 0 ν : X → ℂ) x=(s 1 ν : X → ℂ) x) ∧
      ∀ ν x,((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (p 0 ν i : X → ℂ) x),(s 0 ν : X → ℂ) x) := by
  sorry
end Elasticity

end
end

end OAI
end
