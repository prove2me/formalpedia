-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lowerIndex_eq_zero_iff
-- name    : GroundTheory.LocalField.lowerIndex_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:41.39717+00:00
-- url     : https://prove2.me/theorems/23fc4b45-d6a1-4d9b-b41c-4cbaeca21654
-- title:
--   Local Field: lower Index eq zero iff
-- statement:
--   The Local Field construction uses the lower Index eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L75-L77

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

theorem GroundTheory.LocalField.lowerIndex_eq_zero_iff {σ : L ≃ₐ[K] L} :
    lowerIndex K L σ = 0 ↔ σ ∉ lowerRamificationGroup K L 0 := by sorry
