-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_iff_lowerIndex
-- name    : GroundTheory.LocalField.mem_lowerRamificationGroup_iff_lowerIndex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:12:42.705815+00:00
-- url     : https://prove2.me/theorems/5c009c92-6909-429e-bd84-5d0f75d1bd1e
-- title:
--   Local Field: mem lower Ramification Group iff lower Index
-- statement:
--   The Local Field construction uses the mem lower Ramification Group iff lower Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L43-L46

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

theorem GroundTheory.LocalField.mem_lowerRamificationGroup_iff_lowerIndex {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔ (((i + 1).toNat : ℕ) : ℕ∞) ≤ lowerIndex K L σ := by sorry
