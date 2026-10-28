-- Prove2me | Theorems.Thm_OAI_Elasticity_dn_weak_transport_column
-- name    : OAI.Elasticity.dn_weak_transport_column
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:42:40.639741+00:00
-- url     : https://prove2.me/theorems/2e76d4a7-5986-4025-b91b-2cfa0df205c3
-- title:
--   OAI.Elasticity.dn_weak_transport_column: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Elasticity.dn_weak_transport_column` of [lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Elasticity`, with `open Set MeasureTheory Filter TemperedDistribution`, `open scoped BigOperators SchwartzMap Topology`, `open ElasticityAugmented`, `open ElasticityCoeffBounds (ExteriorConstant)`, `open ElasticityDistribution (Coeff Dist LocalEq AugHilbert leadingRd leadingSd normald)`, `open ElasticityPhysicalAlgebra (phase physical)`, `open ElasticityPhysicalEstimate (physicalAug)`, `open ElasticityNegativeOrder (sobNorm)`, `open ElasticityCGO`):
--
--   ```lean
--   theorem dn_weak_transport_column {Ω B B' : Set X}
--       (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
--       (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
--       (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
--       (hBR : B⊆Metric.ball 0 R) (α β : X) (hα : α≠0)
--       (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
--       (lam m : Fin 2 → X → ℝ)
--       (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
--       (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
--       (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
--       (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
--       (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
--       (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
--       (χ g η : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
--       (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
--       (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
--       (hcη : HasCompactSupport (η : X → ℂ)) (hsη : tsupport (η : X → ℂ)⊆Metric.ball 0 R)
--       (hη : EqOn (η : X → ℂ) 1 B)
--       (a : ℕ → Amplitude Smooth)
--       (ha : PhysicalColumn R hR α β (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) a)
--       (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
--       (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
--         (a (j+1)).1 : Smooth) : X → ℂ) x)
--         (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R)) :
--       let L : Coeff := ⟨smoothOfReal (lam 1) (hl 1),(hcll 1).growth⟩
--       let M : Coeff := ⟨smoothOfReal (m 1) (hm 1),(hclm 1).growth⟩
--       let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
--       ∃ W : AugHilbert,
--         (∀ i,LocalEq B' (leadingRd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
--         LocalEq B' (leadingSd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
--         LocalEq B' (normald θ (fun j => (W j.succ : Dist))) 0 ∧
--         ∀ i,LocalEq (closure Ω)ᶜ (W i : Dist) (localizedLeading R hR a η i : Dist)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Amplitude`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.coord`, `OAI.ElasticityAugmented.div`, `OAI.ElasticityAugmented.normal`, `OAI.ElasticityDistribution.Coeff`, `OAI.ElasticityDistribution.Dist` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.smoothOfReal`, `OAI.ElasticityCGO.PhysicalColumn`, `OAI.ElasticityCGO.localizedLeading`, `OAI.ElasticityCoeffBounds.ExteriorConstant`, `OAI.ElasticityDistribution.AugHilbert`, `OAI.ElasticityDistribution.LocalEq` and `OAI.ElasticityCoeffBounds.ExteriorConstant.growth` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.normald` (definitions bundle `OAIQ6El005` of this split); `OAI.ElasticityDistribution.leadingRd` and `OAI.ElasticityDistribution.leadingSd` (definitions bundle `OAIQ6El006` of this split); `OAI.Elasticity.BoundaryData`, `OAI.Elasticity.DN` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proofs of `OAI_Elasticity_dn_common_leading_frame` and `OAI.Elasticity.dn_smooth_transport_column` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean (declaration OAI.Elasticity.dn_weak_transport_column)

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity
open Set MeasureTheory Filter TemperedDistribution
open scoped BigOperators SchwartzMap Topology
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityDistribution (Coeff Dist LocalEq AugHilbert leadingRd leadingSd normald)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (sobNorm)
open ElasticityCGO

theorem dn_weak_transport_column {Ω B B' : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
    (hBR : B⊆Metric.ball 0 R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g η : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (hcη : HasCompactSupport (η : X → ℂ)) (hsη : tsupport (η : X → ℂ)⊆Metric.ball 0 R)
    (hη : EqOn (η : X → ℂ) 1 B)
    (a : ℕ → Amplitude Smooth)
    (ha : PhysicalColumn R hR α β (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R)) :
    let L : Coeff := ⟨smoothOfReal (lam 1) (hl 1),(hcll 1).growth⟩
    let M : Coeff := ⟨smoothOfReal (m 1) (hm 1),(hclm 1).growth⟩
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    ∃ W : AugHilbert,
      (∀ i,LocalEq B' (leadingRd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0) ∧
      LocalEq B' (leadingSd θ L M (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0 ∧
      LocalEq B' (normald θ (fun j => (W j.succ : Dist))) 0 ∧
      ∀ i,LocalEq (closure Ω)ᶜ (W i : Dist) (localizedLeading R hR a η i : Dist) := by
  sorry
end Elasticity

end

end OAI
end
