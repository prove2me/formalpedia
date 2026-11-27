-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_iff_valuation
-- name    : GroundTheory.LocalField.mem_lowerRamificationGroup_iff_valuation
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:05:21.380293+00:00
-- url     : https://prove2.me/theorems/3edb66c8-1dac-4cb9-9ba3-2fa0efbf141c
-- title:
--   Local Field: mem lower Ramification Group iff valuation
-- statement:
--   The Local Field construction uses the mem lower Ramification Group iff valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L113-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L113-L132

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

theorem GroundTheory.LocalField.mem_lowerRamificationGroup_iff_valuation {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x ∈ 𝒪[L], normalizedValuation L (σ x - x) ≤ WithZero.exp (-(i + 1)) := by sorry
