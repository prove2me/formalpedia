-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_natCast_iff
-- name    : GroundTheory.LocalField.mem_lowerRamificationGroup_natCast_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:21.358708+00:00
-- url     : https://prove2.me/theorems/c59e6766-be96-478a-b2e4-169a62eff391
-- title:
--   Local Field: mem lower Ramification Group nat Cast iff
-- statement:
--   The Local Field construction uses the mem lower Ramification Group nat Cast iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Ramification.lean#L70-L75

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

theorem GroundTheory.LocalField.mem_lowerRamificationGroup_natCast_iff {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (n + 1) := by sorry
