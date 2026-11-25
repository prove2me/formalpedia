-- Prove2me | Theorems.Thm_GroundTheory_LocalField_pow_ringChar_mem_lowerRamificationGroup
-- name    : GroundTheory.LocalField.pow_ringChar_mem_lowerRamificationGroup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:27.676833+00:00
-- url     : https://prove2.me/theorems/5b258af7-bc4f-4354-bc98-d26e3b978d92
-- title:
--   Local Field: pow ring Char mem lower Ramification Group
-- statement:
--   The Local Field construction uses the pow ring Char mem lower Ramification Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L104-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L104-L112

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

theorem GroundTheory.LocalField.pow_ringChar_mem_lowerRamificationGroup {n : ℕ} (hn : 1 ≤ n) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L n) :
    σ ^ ringChar 𝓀[L] ∈ lowerRamificationGroup K L (n + 1 : ℕ) := by sorry
