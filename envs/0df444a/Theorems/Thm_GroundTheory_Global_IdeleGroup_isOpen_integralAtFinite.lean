-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_integralAtFinite
-- name    : GroundTheory.Global.IdeleGroup.isOpen_integralAtFinite
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:50.321453+00:00
-- url     : https://prove2.me/theorems/4ec126b5-65f7-4827-9447-a30d519e2dbf
-- title:
--   Idele Group: is Open integral At Finite
-- statement:
--   The Idele Group construction uses the is Open integral At Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L267-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L267-L269

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

theorem GroundTheory.Global.IdeleGroup.isOpen_integralAtFinite : IsOpen (integralAtFinite K : Set 𝔸[K]) := by sorry
