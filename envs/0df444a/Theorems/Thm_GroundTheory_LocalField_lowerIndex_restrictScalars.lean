-- Prove2me | Theorems.Thm_GroundTheory_LocalField_lowerIndex_restrictScalars
-- name    : GroundTheory.LocalField.lowerIndex_restrictScalars
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:06:34.835463+00:00
-- url     : https://prove2.me/theorems/cf635019-4723-4f44-bdc9-2f3811307260
-- title:
--   Local Field: lower Index restrict Scalars
-- statement:
--   The Local Field construction uses the lower Index restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L131-L133

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
variable (M : IntermediateField K L)

theorem GroundTheory.LocalField.lowerIndex_restrictScalars (σ : L ≃ₐ[M] L) :
    lowerIndex K L (σ.restrictScalars K) = lowerIndex M L σ := by sorry

attribute [defeq] GroundTheory.LocalField.lowerIndex_restrictScalars
