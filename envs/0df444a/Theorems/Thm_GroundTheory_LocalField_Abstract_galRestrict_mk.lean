-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_galRestrict_mk
-- name    : GroundTheory.LocalField.Abstract.galRestrict_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:36.703398+00:00
-- url     : https://prove2.me/theorems/72746898-6f4c-5717-9e2a-ac0ece7dba5b
-- title:
--   Abstract: gal Restrict mk
-- statement:
--   The Abstract construction uses the gal Restrict mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L119-L123

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
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
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]
omit [IsTopologicalGroup G] [CompactSpace G]

theorem GroundTheory.LocalField.Abstract.galRestrict_mk {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) (τ : (K' : Subgroup G)) :
    galRestrict hK hL (τ : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨τ, hK τ.2⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by sorry
