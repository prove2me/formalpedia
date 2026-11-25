-- Prove2me | Theorems.Thm_GroundTheory_Global_ideleNorm_ideleNorm
-- name    : GroundTheory.Global.ideleNorm_ideleNorm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:21.398191+00:00
-- url     : https://prove2.me/theorems/f829090d-3b1b-55a2-9e83-6930cf0b7e7f
-- title:
--   Global: idele Norm idele Norm
-- statement:
--   The Global construction uses the idele Norm idele Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L113-L115

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_InfiniteAdeleRingMapInfiniteAdeleRingMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open AdeleBaseChange
variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem GroundTheory.Global.ideleNorm_ideleNorm (x : IdeleGroup M) :
    ideleNorm K L (ideleNorm L M x) = ideleNorm K M x := by sorry
