-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_hom_eq_rTensor
-- name    : GroundTheory.GroupCoh.whiskerRight_hom_eq_rTensor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:59.492158+00:00
-- url     : https://prove2.me/theorems/fdcc5b66-9fbe-5928-83dd-051f7af79d89
-- title:
--   Group Coh: whisker Right hom eq r Tensor
-- statement:
--   The Group Coh construction uses the whisker Right hom eq r Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L129-L134

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

theorem GroundTheory.GroupCoh.whiskerRight_hom_eq_rTensor (f : A ⟶ B) (Y : Rep.{u} k G) (t : (A ⊗ Y : Rep k G)) :
    (f ▷ Y).hom t = LinearMap.rTensor Y.V f.hom.toLinearMap t := by sorry
