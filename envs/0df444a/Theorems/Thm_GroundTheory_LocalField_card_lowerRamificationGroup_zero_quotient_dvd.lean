-- Prove2me | Theorems.Thm_GroundTheory_LocalField_card_lowerRamificationGroup_zero_quotient_dvd
-- name    : GroundTheory.LocalField.card_lowerRamificationGroup_zero_quotient_dvd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:02.230781+00:00
-- url     : https://prove2.me/theorems/0f90173b-2894-4f08-a6c4-49e6965b18c2
-- title:
--   Local Field: card lower Ramification Group zero quotient dvd
-- statement:
--   The Local Field construction uses the card lower Ramification Group zero quotient dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L61-L67

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
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ
omit hϖ
variable (K L)

theorem GroundTheory.LocalField.card_lowerRamificationGroup_zero_quotient_dvd :
    Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) ∣
        Nat.card 𝓀[L] - 1 := by sorry
