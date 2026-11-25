-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_zpow_smul_mk_mk_eq_iff
-- name    : GroundTheory.LocalField.Abstract.zpow_smul_mk_mk_eq_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:52.1888+00:00
-- url     : https://prove2.me/theorems/1b7c5229-f2ce-4032-880a-a39aefd58e44
-- title:
--   Abstract: zpow smul mk mk eq iff
-- statement:
--   The Abstract construction uses the zpow smul mk mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L168-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean#L168-L179

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
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
open ProfiniteInteger MulAction
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]
omit [IsTopologicalGroup G] [CompactSpace G]

theorem GroundTheory.LocalField.Abstract.zpow_smul_mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (σ x : (K : Subgroup G)) (k : ℤ) :
    ((σ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ k) •
        ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
          _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (x : G)⁻¹ * (σ : G) ^ k * x ∈ (K' : Subgroup G) := by sorry
