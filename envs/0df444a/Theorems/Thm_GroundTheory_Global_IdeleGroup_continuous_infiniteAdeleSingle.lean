-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteAdeleSingle
-- name    : GroundTheory.Global.IdeleGroup.continuous_infiniteAdeleSingle
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:38:34.228617+00:00
-- url     : https://prove2.me/theorems/b8ac2e66-ffd2-4a69-8531-b2940e0280f8
-- title:
--   Idele Group: continuous infinite Adele Single
-- statement:
--   The Idele Group construction uses the continuous infinite Adele Single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L204-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L204-L207

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
omit [NumberField K]

theorem GroundTheory.Global.IdeleGroup.continuous_infiniteAdeleSingle (w : InfinitePlace K) :
    Continuous (infiniteAdeleSingle w) := by sorry
