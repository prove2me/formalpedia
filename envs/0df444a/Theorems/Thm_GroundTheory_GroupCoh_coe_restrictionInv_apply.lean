-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_coe_restrictionInv_apply
-- name    : GroundTheory.GroupCoh.coe_restrictionInv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:56.821466+00:00
-- url     : https://prove2.me/theorems/5522a23a-04b2-524a-9837-7f90fb77f41e
-- title:
--   Group Coh: coe restriction Inv apply
-- statement:
--   The Group Coh construction uses the coe restriction Inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ConjAction.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ConjAction.lean#L124-L126

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ConjAction
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
open CategoryTheory groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

theorem GroundTheory.GroupCoh.coe_restrictionInv_apply (x : groupCohomology A 1) :
    (restrictionInv A S x : groupCohomology (res S.subtype A) 1) =
      (map S.subtype (𝟙 (res S.subtype A)) 1).hom x := by sorry

attribute [defeq] GroundTheory.GroupCoh.coe_restrictionInv_apply
