-- Prove2me | Theorems.Thm_GroundTheory_LocalField_min_le_lowerIndex_mul
-- name    : GroundTheory.LocalField.min_le_lowerIndex_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:18:32.247524+00:00
-- url     : https://prove2.me/theorems/0707a2aa-e13c-4b64-b5b1-7e6efb819da9
-- title:
--   Local Field: min le lower Index mul
-- statement:
--   The Local Field construction uses the min le lower Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L79-L88

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

theorem GroundTheory.LocalField.min_le_lowerIndex_mul (σ τ : L ≃ₐ[K] L) :
    min (lowerIndex K L σ) (lowerIndex K L τ) ≤ lowerIndex K L (σ * τ) := by sorry
