-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsIncl_smul
-- name    : GroundTheory.LocalField.unitsIncl_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:49.238414+00:00
-- url     : https://prove2.me/theorems/b469a2d1-8f9c-484a-9fef-eecf0a9718c2
-- title:
--   Local Field: units Incl smul
-- statement:
--   The Local Field construction uses the units Incl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsGalois.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsGalois.lean#L28-L31

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

theorem GroundTheory.LocalField.unitsIncl_smul (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    unitsIncl L (σ • u) = σ • unitsIncl L u := by sorry
