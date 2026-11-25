-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_range_norm_le_range_norm
-- name    : GroundTheory.LocalField.Abstract.range_norm_le_range_norm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:30.765939+00:00
-- url     : https://prove2.me/theorems/2e6e7ec4-bf16-5f74-ab84-32019c1caa56
-- title:
--   Abstract: range norm le range norm
-- statement:
--   The Abstract construction uses the range norm le range norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L116-L120

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
variable {K L M : Subgroup G}

theorem GroundTheory.LocalField.Abstract.range_norm_le_range_norm (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] :
    (norm A K M).range ≤ (norm A K L).range := by sorry
