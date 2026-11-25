-- Prove2me | Theorems.Thm_GroundTheory_LocalField_gaussSum_term_mul_eq
-- name    : GroundTheory.LocalField.gaussSum_term_mul_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:08.553685+00:00
-- url     : https://prove2.me/theorems/504ba599-7a9d-56e8-9730-4784b3a96cc8
-- title:
--   Local Field: gauss Sum term mul eq
-- statement:
--   The Local Field construction uses the gauss Sum term mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L156-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean#L156-L179

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}

theorem GroundTheory.LocalField.gaussSum_term_mul_eq (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hχ : Continuous χ)
    (hr : ¬ IsUnramifiedChar χ) {x w : Kˣ} (hx : x ∈ unitFiltrationUnits K 0)
    (hw : w ∈ unitFiltrationUnits K (quasiCharConductor χ)) :
    ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * (x * w)) : ℂˣ) : ℂ)⁻¹ *
        (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * (x * w) : Kˣ) : K) : ℂ) =
      ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * x) : ℂˣ) : ℂ)⁻¹ *
        (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * x : Kˣ) : K) : ℂ) := by sorry
