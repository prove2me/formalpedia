-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_normTateZero_mk
-- name    : GroundTheory.LocalField.Abstract.normTateZero_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:40.451403+00:00
-- url     : https://prove2.me/theorems/1f299fb0-8ee3-4245-a894-f2eea318ebb2
-- title:
--   Abstract: norm Tate Zero mk
-- statement:
--   The Abstract construction uses the norm Tate Zero mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L134-L139

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

theorem GroundTheory.LocalField.Abstract.normTateZero_mk {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) (a : fixedModule A (K' : Subgroup G)) :
    normTateZero hK hL hL'K' hLK (QuotientGroup.mk a : tateZero A (K' : Subgroup G) (L' : Subgroup G)) =
      (QuotientGroup.mk (norm A (K : Subgroup G) (K' : Subgroup G) a) :
        tateZero A (K : Subgroup G) (L : Subgroup G)) := by sorry
