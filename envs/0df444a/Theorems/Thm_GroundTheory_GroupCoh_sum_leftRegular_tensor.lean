-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_sum_leftRegular_tensor
-- name    : GroundTheory.GroupCoh.sum_leftRegular_tensor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:43:20.156537+00:00
-- url     : https://prove2.me/theorems/d8794dcf-2f4f-42c0-bd5b-c122056c8b5b
-- title:
--   Group Coh: sum left Regular tensor
-- statement:
--   The Group Coh construction uses the sum left Regular tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L71-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L71-L86

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k G)

theorem GroundTheory.GroupCoh.sum_leftRegular_tensor (t : (leftRegular k G ⊗ B : Rep k G)) :
    ∑ g : G, (leftRegular k G ⊗ B).ρ g
      (TensorProduct.map coeffOneProj LinearMap.id ((leftRegular k G ⊗ B).ρ g⁻¹ t)) = t := by sorry
