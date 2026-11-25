-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_hom_tmul
-- name    : GroundTheory.GroupCoh.whiskerRight_hom_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:32:47.731515+00:00
-- url     : https://prove2.me/theorems/67fcc4f7-b6f6-4761-a127-939ef3312646
-- title:
--   Group Coh: whisker Right hom tmul
-- statement:
--   The Group Coh construction uses the whisker Right hom tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L107-L108

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

theorem GroundTheory.GroupCoh.whiskerRight_hom_tmul (f : A ⟶ B) (Y : Rep.{u} k G) (a : A) (y : Y) :
    (f ▷ Y).hom (a ⊗ₜ[k] y : (A ⊗ Y : Rep k G)) = f.hom a ⊗ₜ[k] y := by sorry
