-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_tateZeroVal_mk
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.tateZeroVal_mk
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:14:12.199099+00:00
-- url     : https://prove2.me/theorems/4089a6b7-bf01-4308-93a2-73e782de3e34
-- title:
--   Class Field Data: tate Zero Val mk
-- statement:
--   The Class Field Data construction uses the tate Zero Val mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Unramified.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Unramified.lean#L142-L145

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
variable {K L : OpenSubgroup G}

theorem GroundTheory.LocalField.Abstract.ClassFieldData.tateZeroVal_mk (hLK : L ≤ K) (a : fixedModule A (K : Subgroup G)) :
    D.tateZeroVal hLK (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      D.valuationMod K (D.relInertiaDegreePNat hLK) a := by sorry
