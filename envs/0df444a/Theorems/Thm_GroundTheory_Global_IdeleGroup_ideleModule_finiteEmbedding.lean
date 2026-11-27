-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ideleModule_finiteEmbedding
-- name    : GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:08.375905+00:00
-- url     : https://prove2.me/theorems/26eee013-f7d8-434e-881b-3d7fc3f90157
-- title:
--   Idele Group: idele Module finite Embedding
-- statement:
--   The Idele Group construction uses the idele Module finite Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L142-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean#L142-L152

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

theorem GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ) :
    (ideleModule K (finiteEmbedding v z) : ℝ) = ‖(z : v.adicCompletion K)‖ := by sorry
