-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_lowerRamificationGroup_eq_bot
-- name    : GroundTheory.LocalField.exists_lowerRamificationGroup_eq_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:28:41.326636+00:00
-- url     : https://prove2.me/theorems/73996711-32e9-4735-9191-86dee79417f6
-- title:
--   Local Field: exists lower Ramification Group eq bot
-- statement:
--   The Local Field construction uses the exists lower Ramification Group eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L155-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L155-L177

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
variable {K L}
variable (K L)

theorem GroundTheory.LocalField.exists_lowerRamificationGroup_eq_bot :
    ∃ n : ℕ, ∀ i : ℤ, n ≤ i → lowerRamificationGroup K L i = ⊥ := by sorry
