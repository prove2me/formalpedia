-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_tateZeroConj_mk
-- name    : GroundTheory.LocalField.Abstract.tateZeroConj_mk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:23.309597+00:00
-- url     : https://prove2.me/theorems/72f1f5c7-8d21-54c4-b1ec-915e05956db3
-- title:
--   Abstract: tate Zero Conj mk
-- statement:
--   The Abstract construction uses the tate Zero Conj mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Functoriality.lean#L180-L183

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

theorem GroundTheory.LocalField.Abstract.tateZeroConj_mk (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    tateZeroConj σ K L (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk (conjFixed σ K a) : tateZero A _ _) := by sorry
