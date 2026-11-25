-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_injective_whiskerRight_tensor_of_flat
-- name    : GroundTheory.GroupCoh.injective_whiskerRight_tensor_of_flat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:44.554221+00:00
-- url     : https://prove2.me/theorems/fb653303-bb4b-492e-b788-9a4aa4f510d5
-- title:
--   Group Coh: injective whisker Right tensor of flat
-- statement:
--   The Group Coh construction uses the injective whisker Right tensor of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L202-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L202-L213

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

theorem GroundTheory.GroupCoh.injective_whiskerRight_tensor_of_flat (Y : Rep.{u} k G)
    (hf : Function.Injective (f ▷ Y).hom) : Function.Injective (f ▷ (V ⊗ Y)).hom := by sorry
