-- Prove2me | Theorems.Thm_OAI_ElasticityCGO_cut_truncation_residual
-- name    : OAI.ElasticityCGO.cut_truncation_residual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:37:41.13522+00:00
-- url     : https://prove2.me/theorems/969da782-8568-4f8d-8b4e-8f6894f43272
-- title:
--   OAI.ElasticityCGO.cut_truncation_residual: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityCGO.cut_truncation_residual` of [lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityCGO`, with `open Set MeasureTheory`, `open scoped BigOperators SchwartzMap`, `open ElasticityAugmented`, `open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply physical phase)`, `open ElasticityDistribution (finiteResidual)`):
--
--   ```lean
--   theorem cut_truncation_residual {U : Set X} (hU : IsOpen U)
--       (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (lam m χ : Smooth)
--       (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
--       (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
--       (h : ℝ) (hh : h≠0) (a : ℕ → Amplitude Smooth)
--       (hR₀ : leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m)
--         (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
--       (hn₀ : normal θ (a 0).1=0)
--       (hrec : ∀ j<8,RecursOn hU θ lam m (a j) (a (j+1))) (i : Fin 3) :
--       EqOn (physical ((h : ℂ)⁻¹ • θ) lam m
--         (fun j => cut χ hc ((truncation (h : ℂ) 8 a).1 j)) i : X → ℂ)
--         (finiteResidual h (fun j => cut χ hc (residual0 lam m (a 8) j))
--           (fun j => cut χ hc (residual1 θ lam m (a 8) j)) i : X → ℂ) U
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Amplitude`, `OAI.ElasticityAugmented.LocalSmooth`, `OAI.ElasticityAugmented.RecursOn`, `OAI.ElasticityAugmented.Smooth`, `OAI.ElasticityAugmented.X`, `OAI.ElasticityAugmented.leadingR`, `OAI.ElasticityAugmented.localAmp`, `OAI.ElasticityAugmented.localCoord`, `OAI.ElasticityAugmented.normal`, `OAI.ElasticityAugmented.restrictSmooth`, `OAI.ElasticityBessel.S`, `OAI.ElasticityBessel.X`, `OAI.ElasticityCGO.S`, `OAI.ElasticityDistribution.S` and `OAI.ElasticityDistribution.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityAugmented.truncation` (definitions bundle `OAIQ6El001` of this split); `OAI.ElasticityCGO.cut`, `OAI.ElasticityCGO.residual0`, `OAI.ElasticityCGO.residual1` and `OAI.ElasticityPhysicalAlgebra.physical` (definitions bundle `OAIQ6El004` of this split); `OAI.ElasticityDistribution.finiteResidual` (definitions bundle `OAIQ6El005` of this split).
--
--   **Used by.** The proof of `OAI.ElasticityCGO.physical_cgo_from_recursion` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Transfer.lean (declaration OAI.ElasticityCGO.cut_truncation_residual)

import Mathlib
import Definitions.Def_OAIQ6El004
import Definitions.Def_OAIQ6El005

section

attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply physical phase)
open ElasticityDistribution (finiteResidual)

theorem cut_truncation_residual {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (h : ℝ) (hh : h≠0) (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m)
      (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<8,RecursOn hU θ lam m (a j) (a (j+1))) (i : Fin 3) :
    EqOn (physical ((h : ℂ)⁻¹ • θ) lam m
      (fun j => cut χ hc ((truncation (h : ℂ) 8 a).1 j)) i : X → ℂ)
      (finiteResidual h (fun j => cut χ hc (residual0 lam m (a 8) j))
        (fun j => cut χ hc (residual1 θ lam m (a 8) j)) i : X → ℂ) U := by
  sorry

end ElasticityCGO

end
end

end OAI
end
