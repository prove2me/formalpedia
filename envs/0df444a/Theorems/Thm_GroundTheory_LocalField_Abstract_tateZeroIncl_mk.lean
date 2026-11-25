-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_tateZeroIncl_mk
-- name    : GroundTheory.LocalField.Abstract.tateZeroIncl_mk
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:50.517616+00:00
-- url     : https://prove2.me/theorems/a441ed7b-7369-59bf-b5f4-6184a376dde0
-- title:
--   Abstract: tate Zero Incl mk
-- statement:
--   The Abstract construction uses the tate Zero Incl mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityNorm.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityNorm.lean#L134-L138

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Functoriality
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem GroundTheory.LocalField.Abstract.tateZeroIncl_mk {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (a : fixedModule A (K : Subgroup G)) :
    tateZeroIncl hLK' hK'K (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk ⟨(a : A), fixedModule_anti hK'K a.2⟩ : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by sorry
