-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_norm_mem_units
-- name    : GroundTheory.LocalField.Abstract.ClassFieldData.norm_mem_units
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:42.802538+00:00
-- url     : https://prove2.me/theorems/ebeb1b3f-4d23-4968-8b26-c9f25b738d22
-- title:
--   Class Field Data: norm mem units
-- statement:
--   The Class Field Data construction uses the norm mem units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Unramified.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Unramified.lean#L178-L180

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

theorem GroundTheory.LocalField.Abstract.ClassFieldData.norm_mem_units (hLK : L ≤ K) {a : fixedModule A (L : Subgroup G)} (ha : a ∈ D.units L) :
    norm A (K : Subgroup G) (L : Subgroup G) a ∈ D.units K := by sorry
