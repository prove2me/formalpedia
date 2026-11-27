-- Prove2me | Theorems.Thm_GroundTheory_Global_ideleClassNorm_ideleClassNorm
-- name    : GroundTheory.Global.ideleClassNorm_ideleClassNorm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:46.305137+00:00
-- url     : https://prove2.me/theorems/3a979c36-ed37-541e-a71c-9608f539057b
-- title:
--   Global: idele Class Norm idele Class Norm
-- statement:
--   The Global construction uses the idele Class Norm idele Class Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L122-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L122-L125

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

theorem GroundTheory.Global.ideleClassNorm_ideleClassNorm (c : IdeleClassGroup M) :
    ideleClassNorm K L (ideleClassNorm L M c) = ideleClassNorm K M c := by sorry
