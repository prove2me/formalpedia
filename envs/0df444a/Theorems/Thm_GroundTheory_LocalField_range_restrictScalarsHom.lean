-- Prove2me | Theorems.Thm_GroundTheory_LocalField_range_restrictScalarsHom
-- name    : GroundTheory.LocalField.range_restrictScalarsHom
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:26.246746+00:00
-- url     : https://prove2.me/theorems/b91486d4-eecc-45f7-838f-ec2a45762902
-- title:
--   Local Field: range restrict Scalars Hom
-- statement:
--   The Local Field construction uses the range restrict Scalars Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LowerIndex.lean#L12-L23

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

theorem GroundTheory.LocalField.range_restrictScalarsHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) :
    (AlgEquiv.restrictScalarsHom K : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L)).range = M.fixingSubgroup := by sorry
