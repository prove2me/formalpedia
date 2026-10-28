-- Prove2me | Theorems.Thm_OAI_ElasticityConic_physical_conic_connections_equal
-- name    : OAI.ElasticityConic.physical_conic_connections_equal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:38:19.956105+00:00
-- url     : https://prove2.me/theorems/f703187b-b0fe-4fa5-9c01-fe773d7c37c0
-- title:
--   OAI.ElasticityConic.physical_conic_connections_equal: intermediate lemma from OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElasticityConic.physical_conic_connections_equal` of [lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElasticityConic`, with `open Set`, `open scoped BigOperators Matrix`, `open ElasticityAugmented`):
--
--   ```lean
--   theorem physical_conic_connections_equal (k r : Fin 2 → Smooth)
--       (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
--       (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
--       {K : Set X} (hK : IsCompact K) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
--       (hχ1 : ∀ x∈K,(χ : X → ℂ) x=1) (x₀ : X) (hx₀ : x₀∉K)
--       (hexk : EqOn (k 0 : X → ℂ) (k 1) Kᶜ) (hexr : EqOn (r 0 : X → ℂ) (r 1) Kᶜ)
--       (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
--       (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
--       (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
--         physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)*G b z-
--         G b z*physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)) :
--       ∀ b z,physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)=
--         physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElasticityAugmented.Smooth` and `OAI.ElasticityAugmented.X` (definitions bundle `OAIQ6El000` of this split); `OAI.ElasticityConic.chartTheta` (definitions bundle `OAIQ6El002` of this split); `OAI.ElasticityAugmented.matrixD` and `OAI.ElasticityConic.physicalChartMatrix` (definitions bundle `OAIQ6El004` of this split).
--
--   **Used by.** The proof of `OAI.Elasticity.dn_global_coefficients_equal` of this split imports it.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Elasticity/Rigidity.lean (declaration OAI.ElasticityConic.physical_conic_connections_equal)

import Mathlib
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
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

theorem physical_conic_connections_equal (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {K : Set X} (hK : IsCompact K) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈K,(χ : X → ℂ) x=1) (x₀ : X) (hx₀ : x₀∉K)
    (hexk : EqOn (k 0 : X → ℂ) (k 1) Kᶜ) (hexr : EqOn (r 0 : X → ℂ) (r 1) Kᶜ)
    (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)*G b z-
      G b z*physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)) :
    ∀ b z,physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1) := by
  sorry
end ElasticityConic

end
end

end OAI
end
