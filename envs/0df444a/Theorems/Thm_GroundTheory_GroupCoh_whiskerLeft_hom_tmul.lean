-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_hom_tmul
-- name    : GroundTheory.GroupCoh.whiskerLeft_hom_tmul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:42.082604+00:00
-- url     : https://prove2.me/theorems/0c5ee30a-92da-52ab-bda0-080f0561c0cc
-- title:
--   Group Coh: whisker Left hom tmul
-- statement:
--   The Group Coh construction uses the whisker Left hom tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L110-L111

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
variable {A B : Rep.{u} k G}

theorem GroundTheory.GroupCoh.whiskerLeft_hom_tmul (Y : Rep.{u} k G) (f : A ⟶ B) (y : Y) (a : A) :
    (Y ◁ f).hom (y ⊗ₜ[k] a : (Y ⊗ A : Rep k G)) = y ⊗ₜ[k] f.hom a := by sorry
