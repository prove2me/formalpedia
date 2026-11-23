-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
-- name    : GroundTheory.LocalField.coe_smul_integerUnits
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:54.456235+00:00
-- url     : https://prove2.me/theorems/09a4446b-05e8-4c6f-a955-882d3427c9c1
-- title:
--   Local Field: coe smul integer Units
-- statement:
--   The Local Field construction uses the coe smul integer Units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsGalois.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsGalois.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
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
open ValuativeRel
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.coe_smul_integerUnits (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    (((σ • u : 𝒪[L]ˣ) : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L) := by sorry

attribute [defeq] GroundTheory.LocalField.coe_smul_integerUnits
