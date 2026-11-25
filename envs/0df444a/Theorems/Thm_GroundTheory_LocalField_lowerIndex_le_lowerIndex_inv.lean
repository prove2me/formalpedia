-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lowerIndex_le_lowerIndex_inv
-- name    : GroundTheory.LocalField.lowerIndex_le_lowerIndex_inv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:41.008643+00:00
-- url     : https://prove2.me/theorems/c6f26062-9821-4bcf-ae6f-7cfc1994d77b
-- title:
--   Local Field: lower Index le lower Index inv
-- statement:
--   The Local Field construction uses the lower Index le lower Index inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L90-L98

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

theorem GroundTheory.LocalField.lowerIndex_le_lowerIndex_inv (σ : L ≃ₐ[K] L) : lowerIndex K L σ ≤ lowerIndex K L σ⁻¹ := by sorry
