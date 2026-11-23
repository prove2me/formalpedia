-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ideleModule_infiniteEmbedding
-- name    : GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:49.095799+00:00
-- url     : https://prove2.me/theorems/3f5c204b-cfa0-4529-a01b-49ca3819a6a6
-- title:
--   Idele Group: idele Module infinite Embedding
-- statement:
--   The Idele Group construction uses the idele Module infinite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L129-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L129-L140

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
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
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}

theorem GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding (w : InfinitePlace K) (z : (w.Completion)ˣ) :
    (ideleModule K (infiniteEmbedding w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by sorry
