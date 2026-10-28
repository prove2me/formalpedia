-- Prove2me | Theorems.Thm_OAI_Elasticity_dn_smooth_transport_column
-- name    : OAI.Elasticity.dn_smooth_transport_column
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:32:23.095893+00:00
-- url     : https://prove2.me/theorems/e3bc8966-2133-45b6-83b0-f2acbeb26bd9
-- title:
--   OAI.Elasticity.dn_smooth_transport_column: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Elasticity.dn_smooth_transport_column` of [lean/OAI/MathematicalPhysics/Elasticity/CommonFrame.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CommonFrame.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Elasticity`, with `open Set MeasureTheory Filter TemperedDistribution`, `open scoped BigOperators SchwartzMap Topology`, `open ElasticityAugmented`, `open ElasticityCoeffBounds (ExteriorConstant)`, `open ElasticityDistribution (Coeff Dist LocalEq AugHilbert )`, `open ElasticityPhysicalAlgebra (phase physical)`, `open ElasticityCGO`):
--
--   ```lean
--   theorem dn_smooth_transport_column {Ω B B' B₀ : Set X}
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
--         (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
--       (hB₀ : IsOpen B₀) (hKB₀ : closure Ω⊆B₀)
--       (ρ : Smooth) (hcρ : HasCompactSupport (ρ : X → ℂ))
--       (hρs : tsupport (ρ : X → ℂ)⊆B') (hρ1 : EqOn (ρ : X → ℂ) 1 B₀) :
--       let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
--       ∃ v : Fin 4 → Smooth,
--         (∀ i,tsupport ((v i-(Fin.cons (a 0).2 (a 0).1 : Fin 4 → Smooth) i : Smooth) : X → ℂ)⊆closure Ω) ∧
--         (∀ i,EqOn (leadingR coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
--           (fun j => v j.succ) (v 0) i).val 0 B') ∧
--         EqOn (leadingS coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
--           (fun j => v j.succ) (v 0)).val 0 B' ∧
--         normal θ (fun j => v j.succ)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Amplitude`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.coord`, `OAI.ElasticityAugmented.div`, `OAI.ElasticityAugmented.leadingR`, `OAI.ElasticityAugmented.leadingS` and `OAI.ElasticityAugmented.normal` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.smoothOfReal`, `OAI.ElasticityCGO.PhysicalColumn` and `OAI.ElasticityCoeffBounds.ExteriorConstant` (definitions bundle `OAIQ6El004` of this split); `OAI.Elasticity.BoundaryData`, `OAI.Elasticity.DN` and `OAI.Elasticity.X` (the published bundle `Def_ElasticityUniqueness`).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_common_normal_frame` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/CommonFrame.lean (declaration OAI.Elasticity.dn_smooth_transport_column)

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
open Set MeasureTheory Filter TemperedDistribution
open scoped BigOperators SchwartzMap Topology
namespace Elasticity
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityDistribution (Coeff Dist LocalEq AugHilbert )
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityCGO

theorem dn_smooth_transport_column {Ω B B' B₀ : Set X}
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
      (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    (hB₀ : IsOpen B₀) (hKB₀ : closure Ω⊆B₀)
    (ρ : Smooth) (hcρ : HasCompactSupport (ρ : X → ℂ))
    (hρs : tsupport (ρ : X → ℂ)⊆B') (hρ1 : EqOn (ρ : X → ℂ) 1 B₀) :
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    ∃ v : Fin 4 → Smooth,
      (∀ i,tsupport ((v i-(Fin.cons (a 0).2 (a 0).1 : Fin 4 → Smooth) i : Smooth) : X → ℂ)⊆closure Ω) ∧
      (∀ i,EqOn (leadingR coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
        (fun j => v j.succ) (v 0) i).val 0 B') ∧
      EqOn (leadingS coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
        (fun j => v j.succ) (v 0)).val 0 B' ∧
      normal θ (fun j => v j.succ)=0 := by
  sorry
end Elasticity

end
end

end OAI
end
