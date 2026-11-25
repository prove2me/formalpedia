-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isPGroup_lowerRamificationGroup_one
-- name    : GroundTheory.LocalField.isPGroup_lowerRamificationGroup_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:21.523102+00:00
-- url     : https://prove2.me/theorems/4dbd89a4-d03d-4962-82ed-783f2d96b510
-- title:
--   Local Field: is PGroup lower Ramification Group one
-- statement:
--   The Local Field construction uses the is PGroup lower Ramification Group one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L116-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L116-L132

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
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
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)

theorem GroundTheory.LocalField.isPGroup_lowerRamificationGroup_one :
    IsPGroup (ringChar 𝓀[K]) (lowerRamificationGroup K L 1) := by sorry
