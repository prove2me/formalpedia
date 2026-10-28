-- Prove2me | Theorems.Thm_OAI_ElasticityCGO_physical_cgo_from_recursion
-- name    : OAI.ElasticityCGO.physical_cgo_from_recursion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:37:32.111562+00:00
-- url     : https://prove2.me/theorems/811bbfc5-b89e-4ee4-9b9c-b11e481a56f9
-- title:
--   OAI.ElasticityCGO.physical_cgo_from_recursion: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityCGO.physical_cgo_from_recursion` of [lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityCGO`, with `open MeasureTheory Set TemperedDistribution`, `open scoped SchwartzMap ENNReal BigOperators`, `open ElasticityAugmented`, `open ElasticityCoeffBounds (ExteriorConstant)`, `open ElasticityRegularity (sobolevInjection)`, `open ElasticityPhysicalAlgebra (phase physical)`, `open ElasticityDistribution (HV Dist divd)`):
--
--   ```lean
--   theorem physical_cgo_from_recursion (R : ℝ) (hR : 1≤R)
--       (Ω U : Set X) (hΩ : Ω⊆Metric.closedBall 0 R) (hU : IsOpen U) (hsub : U⊆Ω)
--       (α β : X) (hα : α≠0)
--       (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
--       (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
--       (hrl : ∀ x,star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
--       (hrm : ∀ x,star ((m : X → ℂ) x)=(m : X → ℂ) x)
--       (hm0 : ∀ x,(m : X → ℂ) x≠0)
--       (he0 : ∀ x,((lam+m+m : Smooth) : X → ℂ) x≠0)
--       (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
--       (hcχ : ∀ i,HasCompactSupport (χ i))
--       (hnest : ∀ i : Fin 4,EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
--       (hs : ∀ i,tsupport (χ i)⊆Ω) (h1 : EqOn (χ 0) 1 U)
--       (a : ℕ → Amplitude Smooth)
--       (hR₀ : leadingR (localCoord hU) (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
--         (restrictSmooth U lam) (restrictSmooth U m) (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
--       (hn₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
--       (hrec : ∀ j<8,RecursOn hU (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m (a j) (a (j+1))) :
--       ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
--         ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
--           (∀ i,∀ᵐ x ∂(volume : Measure X),x∈U → w i x=v i x) ∧
--           (∀ i,EqOn (physical (phase h α β) lam m
--             ((fun j => cut ⟨χ 0,hχ 0⟩ (hcχ 0) ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 U) ∧
--           (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
--             ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
--               (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
--           ‖w‖≤C*h^7 ∧ ‖q‖≤C*h
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Amplitude`, `OAI.ElasticityAugmented.LocalSmooth`, `OAI.ElasticityAugmented.RecursOn`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.leadingR`, `OAI.ElasticityAugmented.localAmp`, `OAI.ElasticityAugmented.localCoord`, `OAI.ElasticityAugmented.normal`, `OAI.ElasticityAugmented.restrictSmooth`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X`, `OAI.ElasticityCGO.S`, `OAI.ElasticityDistribution.Dist`, `OAI.ElasticityDistribution.X`, `OAI.ElasticityPhysicalDual.H` and `OAI.ElasticityPhysicalDual.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.truncation` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityRegularity.sobolevInjection` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityCGO.cut`, `OAI.ElasticityCoeffBounds.ExteriorConstant`, `OAI.ElasticityDistribution.H`, `OAI.ElasticityDistribution.HV`, `OAI.ElasticityDistribution.divd`, `OAI.ElasticityPhysicalAlgebra.phase` and `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proofs of `OAI_Elasticity_dn_common_leading_frame` and `OAI.Elasticity.dn_common_normal_frame` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/PhysicalCGO.lean (declaration OAI.ElasticityCGO.physical_cgo_from_recursion)

import Mathlib
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCGO

section
open MeasureTheory Set TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityRegularity (sobolevInjection)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityDistribution (HV Dist divd)

theorem physical_cgo_from_recursion (R : ℝ) (hR : 1≤R)
    (Ω U : Set X) (hΩ : Ω⊆Metric.closedBall 0 R) (hU : IsOpen U) (hsub : U⊆Ω)
    (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (hrl : ∀ x,star ((lam : X → ℂ) x)=(lam : X → ℂ) x)
    (hrm : ∀ x,star ((m : X → ℂ) x)=(m : X → ℂ) x)
    (hm0 : ∀ x,(m : X → ℂ) x≠0)
    (he0 : ∀ x,((lam+m+m : Smooth) : X → ℂ) x≠0)
    (χ : Fin 5 → X → ℂ) (hχ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (χ i))
    (hcχ : ∀ i,HasCompactSupport (χ i))
    (hnest : ∀ i : Fin 4,EqOn (χ i.succ) 1 (tsupport (χ i.castSucc)))
    (hs : ∀ i,tsupport (χ i)⊆Ω) (h1 : EqOn (χ 0) 1 U)
    (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (restrictSmooth U lam) (restrictSmooth U m) (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,RecursOn hU (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) lam m (a j) (a (j+1))) :
    ∃ C h₀ : ℝ, 0<C ∧ 0<h₀ ∧ ∀ h : ℝ,0<h → h≤h₀ →
      ∃ w : ElasticityPhysicalDual.H,∃ q : HV,∃ v : Fin 3 → S,
        (∀ i,∀ᵐ x ∂(volume : Measure X),x∈U → w i x=v i x) ∧
        (∀ i,EqOn (physical (phase h α β) lam m
          ((fun j => cut ⟨χ 0,hχ 0⟩ (hcχ 0) ((truncation (h : ℂ) 8 a).1 j))-v) i : X → ℂ) 0 U) ∧
        (∀ i,sobolevInjection 1 (q i)=smulLeftCLM ℂ (χ 0)
          ((Fin.cons (divd (phase h α β) (fun j => (w j : Dist)))
            (fun j => (w j : Dist)) : Fin 4 → Dist) i)) ∧
        ‖w‖≤C*h^7 ∧ ‖q‖≤C*h := by
  sorry
end
open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

end ElasticityCGO

end

end OAI
end
