-- Prove2me | Theorems.Thm_OAI_ElasticityGeneralSlicing_cylinder_weak_slices
-- name    : OAI.ElasticityGeneralSlicing.cylinder_weak_slices
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:28:30.608885+00:00
-- url     : https://prove2.me/theorems/603fc0ab-056f-42dd-bbe2-697b71ce68a0
-- title:
--   OAI.ElasticityGeneralSlicing.cylinder_weak_slices: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityGeneralSlicing.cylinder_weak_slices` of [lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityGeneralSlicing`, with `open Set MeasureTheory TemperedDistribution`, `open scoped SchwartzMap ENNReal LineDeriv`, `open ElasticityPlanar`):
--
--   ```lean
--   theorem cylinder_weak_slices (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
--       (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
--       (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
--         Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0) :
--       ∀ᵐ t : P, MemLp (fun z => u (t,z)) 2 volume ∧
--         MemLp (fun z => w (t,z)) 2 volume ∧
--         ∀ φ : Test, (∫ z, φ z*w (t,z))=(∫ z, testDbar φ z*u (t,z))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityGeneralSlicing.cylinder_temperate`, `OAI.ElasticityGeneralSlicing.testDbar` and `OAI.ElasticityPlanar.Test` (definitions bundle `OAIQ6El002` of this split).
--
--   **Used by.** The proofs of `OAI_ElasticityGeneralSlicing_coupled_slice_equations`, `OAI.ElasticityGeneralSlicing.smooth_cylinder_representative` and `OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder` of this split import it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/WeakLimits.lean (declaration OAI.ElasticityGeneralSlicing.cylinder_weak_slices)

import Mathlib
import Definitions.Def_OAIQ6El002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar

theorem cylinder_weak_slices (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
    (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P, MemLp (fun z => u (t,z)) 2 volume ∧
      MemLp (fun z => w (t,z)) 2 volume ∧
      ∀ φ : Test, (∫ z, φ z*w (t,z))=(∫ z, testDbar φ z*u (t,z)) := by
  sorry

end ElasticityGeneralSlicing

end

end OAI
end
