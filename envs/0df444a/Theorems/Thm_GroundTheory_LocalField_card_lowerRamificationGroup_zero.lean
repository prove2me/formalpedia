-- Prove2me | Theorems.Thm_GroundTheory_LocalField_card_lowerRamificationGroup_zero
-- name    : GroundTheory.LocalField.card_lowerRamificationGroup_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:17:17.366186+00:00
-- url     : https://prove2.me/theorems/ab87e52f-18bf-443d-aa06-77c2ee9da94e
-- title:
--   Local Field: card lower Ramification Group zero
-- statement:
--   The Local Field construction uses the card lower Ramification Group zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L157-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L157-L160

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
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
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)

theorem GroundTheory.LocalField.card_lowerRamificationGroup_zero [IsGalois K L] :
    Nat.card (lowerRamificationGroup K L 0) = ramificationIndex K L := by sorry
