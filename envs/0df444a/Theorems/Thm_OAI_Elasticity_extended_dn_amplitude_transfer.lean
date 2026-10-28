-- Prove2me | Theorems.Thm_OAI_Elasticity_extended_dn_amplitude_transfer
-- name    : OAI.Elasticity.extended_dn_amplitude_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:32:45.769315+00:00
-- url     : https://prove2.me/theorems/c30d9620-7b3a-430e-9a1b-80a21f544038
-- title:
--   OAI.Elasticity.extended_dn_amplitude_transfer: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Elasticity.extended_dn_amplitude_transfer` of [lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Elasticity`, with `open Set MeasureTheory`, `open scoped BigOperators SchwartzMap`, `open ElasticityAugmented (Smooth smoothOfReal smooth_coe)`, `open ElasticityCoeffBounds`, `open ElasticityDistribution (Coeff eval)`, `open ElasticityPhysicalAlgebra (physical)`, `open ElasticityCGO (expCut)`):
--
--   ```lean
--   theorem extended_dn_amplitude_transfer {Ω B B' : Set X}
--       (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
--       (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
--       (lam m : Fin 2 → X → ℝ)
--       (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
--       (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
--       (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
--       (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
--       (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
--       (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
--       (χ g : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
--       (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
--       (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
--       (z : Fin 3 → ℂ) (u : Fin 3 → SchwartzMap X ℂ)
--       (hu : ∀ i,EqOn (physical z (fun x => (lam 0 x : ℂ)) (fun x => (m 0 x : ℂ)) u i : X → ℂ) 0 B) :
--       ∃ v : Fin 3 → SchwartzMap X ℂ,
--         (∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆closure Ω) ∧
--         (∀ i,EqOn (physical z (fun x => (lam 1 x : ℂ)) (fun x => (m 1 x : ℂ)) v i : X → ℂ) 0 B')
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X` and `OAI.ElasticityPhysicalAlgebra.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.smoothOfReal`, `OAI.ElasticityCoeffBounds.ExteriorConstant` and `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split); `OAI.Elasticity.BoundaryData`, `OAI.Elasticity.DN` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proofs of `OAI.Elasticity.dn_weak_transport_column` and `OAI_Elasticity_extended_dn_compact_comparison` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean (declaration OAI.Elasticity.extended_dn_amplitude_transfer)

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity
open Set MeasureTheory
open scoped BigOperators SchwartzMap
open ElasticityAugmented (Smooth smoothOfReal smooth_coe)
open ElasticityCoeffBounds
open ElasticityDistribution (Coeff eval)
open ElasticityPhysicalAlgebra (physical)
open ElasticityCGO (expCut)

theorem extended_dn_amplitude_transfer {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (z : Fin 3 → ℂ) (u : Fin 3 → SchwartzMap X ℂ)
    (hu : ∀ i,EqOn (physical z (fun x => (lam 0 x : ℂ)) (fun x => (m 0 x : ℂ)) u i : X → ℂ) 0 B) :
    ∃ v : Fin 3 → SchwartzMap X ℂ,
      (∀ i,tsupport (v i-u i : SchwartzMap X ℂ)⊆closure Ω) ∧
      (∀ i,EqOn (physical z (fun x => (lam 1 x : ℂ)) (fun x => (m 1 x : ℂ)) v i : X → ℂ) 0 B') := by
  sorry

open ElasticityPhysicalAlgebra (phase)
end Elasticity

end

end OAI
end
