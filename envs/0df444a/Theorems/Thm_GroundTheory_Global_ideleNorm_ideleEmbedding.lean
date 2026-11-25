-- Prove2me | Theorems.Thm_GroundTheory_Global_ideleNorm_ideleEmbedding
-- name    : GroundTheory.Global.ideleNorm_ideleEmbedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:19.512038+00:00
-- url     : https://prove2.me/theorems/f94ab0be-e5a6-52e8-90d2-ef2417bcbc9a
-- title:
--   Global: idele Norm idele Embedding
-- statement:
--   The Global construction uses the idele Norm idele Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L186-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L186-L188

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

theorem GroundTheory.Global.ideleNorm_ideleEmbedding (x : IdeleGroup K) :
    ideleNorm K L (ideleEmbedding K L x) = x ^ Module.finrank K L := by sorry
