-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerRight_retract
-- name    : GroundTheory.GroupCoh.whiskerRight_retract
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:31:48.865692+00:00
-- url     : https://prove2.me/theorems/ae51d326-e8e4-4962-a189-cfdd5bdf5c1c
-- title:
--   Group Coh: whisker Right retract
-- statement:
--   The Group Coh construction uses the whisker Right retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L113-L119

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

theorem GroundTheory.GroupCoh.whiskerRight_retract (f : A ⟶ B) (r : B.V →ₗ[k] A.V)
    (hr : ∀ a, r (f.hom a) = a) (Y : Rep.{u} k G) (t : (A ⊗ Y : Rep k G)) :
    LinearMap.rTensor Y.V r ((f ▷ Y).hom t) = t := by sorry
