-- Prove2me | Theorems.Thm_OAI_ElasticityCGO_transferred_amplitude
-- name    : OAI.ElasticityCGO.transferred_amplitude
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:37:29.0331+00:00
-- url     : https://prove2.me/theorems/29fbe49a-8636-4a35-a55a-8215699a2520
-- title:
--   OAI.ElasticityCGO.transferred_amplitude: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityCGO.transferred_amplitude` of [lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityCGO`, with `open Set`, `open scoped BigOperators SchwartzMap`, `open ElasticityAugmented`, `open ElasticityPhysicalAlgebra (physical shiftD )`, `open ElasticityCarleman (phaseCLM)`):
--
--   ```lean
--   theorem transferred_amplitude {B K : Set X} (hB : IsOpen B)
--       (lam m χ : Smooth) (hl : (lam : X → ℂ).HasTemperateGrowth)
--       (hm : (m : X → ℂ).HasTemperateGrowth) (hc : HasCompactSupport (χ : X → ℂ))
--       (hχ : EqOn (χ : X → ℂ) 1 B) (z : Fin 3 → ℂ) (u F H : Fin 3 → S)
--       (hF : ∀ i x,x∈B → F i x=Complex.exp (phaseCLM z x)*u i x)
--       (hH : ∀ i,tsupport (H i : X → ℂ)⊆K)
--       (hsol : ∀ i,EqOn (physical 0 lam m (F+H) i : X → ℂ) 0 B) :
--       ∃ v : Fin 3 → S,
--         (∀ i,tsupport (v i-u i : S)⊆K) ∧
--         (∀ i,EqOn (physical z lam m v i : X → ℂ) 0 B) ∧
--         (∀ i x,x∈B → Complex.exp (phaseCLM z x)*v i x=F i x+H i x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X`, `OAI.ElasticityCGO.S`, `OAI.ElasticityCarleman.X` and `OAI.ElasticityCarleman.phaseCLM` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.Elasticity.extended_dn_amplitude_transfer` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean (declaration OAI.ElasticityCGO.transferred_amplitude)

import Mathlib
import Definitions.Def_OAIQ6El004

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (physical shiftD )
open ElasticityCarleman (phaseCLM)

theorem transferred_amplitude {B K : Set X} (hB : IsOpen B)
    (lam m χ : Smooth) (hl : (lam : X → ℂ).HasTemperateGrowth)
    (hm : (m : X → ℂ).HasTemperateGrowth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 B) (z : Fin 3 → ℂ) (u F H : Fin 3 → S)
    (hF : ∀ i x,x∈B → F i x=Complex.exp (phaseCLM z x)*u i x)
    (hH : ∀ i,tsupport (H i : X → ℂ)⊆K)
    (hsol : ∀ i,EqOn (physical 0 lam m (F+H) i : X → ℂ) 0 B) :
    ∃ v : Fin 3 → S,
      (∀ i,tsupport (v i-u i : S)⊆K) ∧
      (∀ i,EqOn (physical z lam m v i : X → ℂ) 0 B) ∧
      (∀ i x,x∈B → Complex.exp (phaseCLM z x)*v i x=F i x+H i x) := by
  sorry

end ElasticityCGO

end
end

end OAI
end
