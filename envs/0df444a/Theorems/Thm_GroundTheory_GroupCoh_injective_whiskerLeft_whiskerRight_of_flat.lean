-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_injective_whiskerLeft_whiskerRight_of_flat
-- name    : GroundTheory.GroupCoh.injective_whiskerLeft_whiskerRight_of_flat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:14:50.07633+00:00
-- url     : https://prove2.me/theorems/5af79ebd-676d-41ef-9099-818755bcf898
-- title:
--   Group Coh: injective whisker Left whisker Right of flat
-- statement:
--   The Group Coh construction uses the injective whisker Left whisker Right of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L215-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L215-L226

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
variable (V : Rep.{u} k G) [Module.Flat k V.V] {X₁ X₂ : Rep.{u} k G} (f : X₁ ⟶ X₂)

theorem GroundTheory.GroupCoh.injective_whiskerLeft_whiskerRight_of_flat (Y : Rep.{u} k G)
    (hf : Function.Injective (f ▷ Y).hom) : Function.Injective ((V ◁ f) ▷ Y).hom := by sorry
