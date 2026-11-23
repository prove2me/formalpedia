-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_leftRegular_tensor
-- name    : GroundTheory.GroupCoh.tateAcyclic_leftRegular_tensor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:06.741251+00:00
-- url     : https://prove2.me/theorems/4ed769bb-5469-4acf-a5ba-dbfc2e719e4c
-- title:
--   Group Coh: tate Acyclic left Regular tensor
-- statement:
--   The Group Coh construction uses the tate Acyclic left Regular tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InducedNorm.lean#L88-L89

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

theorem GroundTheory.GroupCoh.tateAcyclic_leftRegular_tensor : TateAcyclic (leftRegular k G ⊗ B) := by sorry
