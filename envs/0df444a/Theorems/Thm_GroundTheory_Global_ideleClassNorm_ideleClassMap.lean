-- Prove2me | Theorems.Thm_GroundTheory_Global_ideleClassNorm_ideleClassMap
-- name    : GroundTheory.Global.ideleClassNorm_ideleClassMap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:57.435003+00:00
-- url     : https://prove2.me/theorems/50521ad9-dd26-46c3-a5f9-f0a974acece0
-- title:
--   Global: idele Class Norm idele Class Map
-- statement:
--   The Global construction uses the idele Class Norm idele Class Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L228-L231

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open AdeleBaseChange
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}

theorem GroundTheory.Global.ideleClassNorm_ideleClassMap (c : IdeleClassGroup K) :
    ideleClassNorm K L (ideleClassMap K L c) = c ^ Module.finrank K L := by sorry
