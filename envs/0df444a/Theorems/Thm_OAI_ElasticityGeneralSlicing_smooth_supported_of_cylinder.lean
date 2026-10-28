-- Prove2me | Theorems.Thm_OAI_ElasticityGeneralSlicing_smooth_supported_of_cylinder
-- name    : OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:29:17.388839+00:00
-- url     : https://prove2.me/theorems/456a24ea-9303-4408-8dc6-b2bf257e3b33
-- title:
--   OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder` of [lean/OAI/MathematicalPhysics/Elasticity/Supported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityGeneralSlicing`, with `open Set MeasureTheory TemperedDistribution Filter`, `open scoped SchwartzMap ENNReal BigOperators Topology LineDeriv`, `open ElasticityPlanar ElasticityRegularity`, `open ElasticityPlanarDistribution (Dist dbar)`):
--
--   ```lean
--   theorem smooth_supported_of_cylinder (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
--       (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
--       (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
--       (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
--       (hfs : ∀ i t z,z∉K → f i (t,z)=0)
--       (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
--       (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
--       (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
--       (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
--       (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
--       (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
--         Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
--       ∃ v : P → n → Test,
--         (∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
--         (∀ t i,tsupport (v t i : ℂ → ℂ)⊆S) ∧
--         ∀ t i z,schwartzDbar (toSchwartz (v t i)) z+∑ j,a i j (t,z)*v t j z=f i (t,z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityGeneralSlicing.cylinder_temperate`, `OAI.ElasticityPlanar.Test` and `OAI.ElasticityPlanar.toSchwartz` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityPlanar.schwartzDbar` (definitions bundle `OAIQ6El003` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityGeneralSlicing.smooth_cylinder_representative` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean (declaration OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder)

import Mathlib
import Definitions.Def_OAIQ6El002
import Definitions.Def_OAIQ6El003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal BigOperators Topology LineDeriv
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar ElasticityRegularity
open ElasticityPlanarDistribution (Dist dbar)
variable {n : Type*} [Fintype n]

theorem smooth_supported_of_cylinder (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i t z,z∉K → f i (t,z)=0)
    (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
    (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
    (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
    (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
    (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
    ∃ v : P → n → Test,
      (∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      (∀ t i,tsupport (v t i : ℂ → ℂ)⊆S) ∧
      ∀ t i z,schwartzDbar (toSchwartz (v t i)) z+∑ j,a i j (t,z)*v t j z=f i (t,z) := by
  sorry
end ElasticityGeneralSlicing

end

end OAI
end
