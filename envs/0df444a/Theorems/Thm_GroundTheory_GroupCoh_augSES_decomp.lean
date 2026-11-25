-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_augSES_decomp
-- name    : GroundTheory.GroupCoh.augSES_decomp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:55.559915+00:00
-- url     : https://prove2.me/theorems/b43ff2af-1077-5e5d-80f7-6fa1bdca7064
-- title:
--   Group Coh: aug SES decomp
-- statement:
--   The Group Coh construction uses the aug SES decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L304-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L304-L316

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

theorem GroundTheory.GroupCoh.augSES_decomp (X : Rep.{u} k G) (t : (Rep.leftRegular k G ⊗ X : Rep k G)) :
    (augIdealι k G ▷ X).hom (LinearMap.rTensor X.V (augIdealRetract k G) t) +
      (MonoidAlgebra.single 1 1 ⊗ₜ[k] (augX X).hom t : (Rep.leftRegular k G ⊗ X : Rep k G)) = t := by sorry
