-- Prove2me | Theorems.Thm_OAI_ElasticityPlanar_supported_parameter_inversion
-- name    : OAI.ElasticityPlanar.supported_parameter_inversion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:41:22.475391+00:00
-- url     : https://prove2.me/theorems/6105c488-cb3a-41c9-ac29-26ea3845dc8f
-- title:
--   OAI.ElasticityPlanar.supported_parameter_inversion: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityPlanar.supported_parameter_inversion` of [lean/OAI/MathematicalPhysics/Elasticity/Supported.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityPlanar`, with `open Set MeasureTheory TemperedDistribution`, `open scoped SchwartzMap ENNReal BigOperators`, `open ElasticityRegularity`):
--
--   ```lean
--   theorem supported_parameter_inversion {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
--       (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
--       (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
--       (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
--       (hfs : ∀ i p z, z∉K → f i (p,z)=0)
--       {D : Set P} (hD : Dense D)
--       (hex : ∀ p∈D, ∃ w : Hilbert n, ∀ i,
--         planarOperator (fun i j z => a i j (p,z)) i w=
--           (toSchwartz ⟨fun z => f i (p,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
--             compact_slice hK (f i) (hfs i) p⟩⟩ : 𝓢'(ℂ,ℂ)) ∧
--         LocalEqual Sᶜ (entryInjection i w) 0) :
--       ∃ v : P → n → Test,
--         (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
--         (∀ p i, tsupport (v p i : ℂ → ℂ)⊆S) ∧
--         ∀ p i z, schwartzDbar (toSchwartz (v p i)) z+
--           ∑ j, a i j (p,z)*v p j z=f i (p,z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityPlanar.Hilbert`, `OAI.ElasticityPlanar.Test` and `OAI.ElasticityPlanar.toSchwartz` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityPlanar.schwartzDbar`, `OAI.ElasticityRegularity.LocalEqual` and `OAI.ElasticityRegularity.compact_slice` (definitions bundle `OAIQ6El003` of this split); `OAI.ElasticityPlanar.entryInjection` and `OAI.ElasticityPlanar.planarOperator` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proofs of `OAI.ElasticityAugmented.supported_matrix_smooth` and `OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Supported.lean (declaration OAI.ElasticityPlanar.supported_parameter_inversion)

import Mathlib
import Definitions.Def_OAIQ6El005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
theorem supported_parameter_inversion {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z, z∉K → a i j (p,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i p z, z∉K → f i (p,z)=0)
    {D : Set P} (hD : Dense D)
    (hex : ∀ p∈D, ∃ w : Hilbert n, ∀ i,
      planarOperator (fun i j z => a i j (p,z)) i w=
        (toSchwartz ⟨fun z => f i (p,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) p⟩⟩ : 𝓢'(ℂ,ℂ)) ∧
      LocalEqual Sᶜ (entryInjection i w) 0) :
    ∃ v : P → n → Test,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      (∀ p i, tsupport (v p i : ℂ → ℂ)⊆S) ∧
      ∀ p i z, schwartzDbar (toSchwartz (v p i)) z+
        ∑ j, a i j (p,z)*v p j z=f i (p,z) := by
  sorry

end ElasticityPlanar

end

end OAI
end
