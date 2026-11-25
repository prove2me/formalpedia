-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_eq_top
-- name    : GroundTheory.LocalField.lowerRamificationGroup_eq_top
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:52.901021+00:00
-- url     : https://prove2.me/theorems/15b54d2f-4c60-4e5d-9c6e-2767b03ba4ed
-- title:
--   Local Field: lower Ramification Group eq top
-- statement:
--   The Local Field construction uses the lower Ramification Group eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L83-L88

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)

theorem GroundTheory.LocalField.lowerRamificationGroup_eq_top {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup K L i = ⊤ := by sorry
