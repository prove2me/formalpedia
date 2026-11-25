-- Prove2me | Theorems.Thm_GroundTheory_Global_ideleEmbedding_ideleEmbedding
-- name    : GroundTheory.Global.ideleEmbedding_ideleEmbedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:00.474383+00:00
-- url     : https://prove2.me/theorems/fcd1bb26-2cd0-425b-9fc7-f8b1322e3614
-- title:
--   Global: idele Embedding idele Embedding
-- statement:
--   The Global construction uses the idele Embedding idele Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L109-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean#L109-L111

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

theorem GroundTheory.Global.ideleEmbedding_ideleEmbedding (x : IdeleGroup K) :
    ideleEmbedding L M (ideleEmbedding K L x) = ideleEmbedding K M x := by sorry
