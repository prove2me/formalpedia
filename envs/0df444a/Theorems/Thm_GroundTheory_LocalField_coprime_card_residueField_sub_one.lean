-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coprime_card_residueField_sub_one
-- name    : GroundTheory.LocalField.coprime_card_residueField_sub_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:15.239724+00:00
-- url     : https://prove2.me/theorems/3c1d8adb-b850-453c-af26-57aea4a2152d
-- title:
--   Local Field: coprime card residue Field sub one
-- statement:
--   The Local Field construction uses the coprime card residue Field sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L71-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L71-L81

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
variable {K L}

theorem GroundTheory.LocalField.coprime_card_residueField_sub_one : Nat.Coprime (Nat.card 𝓀[L] - 1) (ringChar 𝓀[L]) := by sorry
