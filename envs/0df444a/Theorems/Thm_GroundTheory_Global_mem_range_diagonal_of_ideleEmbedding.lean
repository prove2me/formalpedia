-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_range_diagonal_of_ideleEmbedding
-- name    : GroundTheory.Global.mem_range_diagonal_of_ideleEmbedding
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:08.788239+00:00
-- url     : https://prove2.me/theorems/493bf860-3579-5fc0-b12f-6bbc5a560929
-- title:
--   Global: mem range diagonal of idele Embedding
-- statement:
--   The Global construction uses the mem range diagonal of idele Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L233-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean#L233-L244

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

theorem GroundTheory.Global.mem_range_diagonal_of_ideleEmbedding {x : IdeleGroup K}
    (hx : ideleEmbedding K L x ∈ (IdeleGroup.diagonal L).range) :
    x ∈ (IdeleGroup.diagonal K).range := by sorry
