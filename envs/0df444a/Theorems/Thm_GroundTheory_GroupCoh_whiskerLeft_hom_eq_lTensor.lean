-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_hom_eq_lTensor
-- name    : GroundTheory.GroupCoh.whiskerLeft_hom_eq_lTensor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:33:07.377873+00:00
-- url     : https://prove2.me/theorems/b4cb6133-dc7f-409b-9b20-8c7f7fcccae4
-- title:
--   Group Coh: whisker Left hom eq l Tensor
-- statement:
--   The Group Coh construction uses the whisker Left hom eq l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L136-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L136-L141

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

theorem GroundTheory.GroupCoh.whiskerLeft_hom_eq_lTensor (Y : Rep.{u} k G) (f : A ⟶ B) (t : (Y ⊗ A : Rep k G)) :
    (Y ◁ f).hom t = LinearMap.lTensor Y.V f.hom.toLinearMap t := by sorry
