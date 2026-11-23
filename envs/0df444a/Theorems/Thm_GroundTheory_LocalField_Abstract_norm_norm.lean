-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm
-- name    : GroundTheory.LocalField.Abstract.norm_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:02.014604+00:00
-- url     : https://prove2.me/theorems/6531194a-6ab4-4e70-9662-0cbbb33622fa
-- title:
--   Abstract: norm norm
-- statement:
--   The Abstract construction uses the norm norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L64-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/UniqueQuotientSubgroupOfSelf.lean#L64-L114

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

theorem GroundTheory.LocalField.Abstract.norm_norm (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] (a : fixedModule A M) :
    norm A K L (norm A L M a) = norm A K M a := by sorry
