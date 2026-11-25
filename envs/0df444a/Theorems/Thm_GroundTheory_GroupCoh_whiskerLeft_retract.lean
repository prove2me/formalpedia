-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_whiskerLeft_retract
-- name    : GroundTheory.GroupCoh.whiskerLeft_retract
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:53.289535+00:00
-- url     : https://prove2.me/theorems/48fd426e-a9d9-5827-aa81-78e23a186621
-- title:
--   Group Coh: whisker Left retract
-- statement:
--   The Group Coh construction uses the whisker Left retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L121-L127

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

theorem GroundTheory.GroupCoh.whiskerLeft_retract (f : A ⟶ B) (r : B.V →ₗ[k] A.V)
    (hr : ∀ a, r (f.hom a) = a) (Y : Rep.{u} k G) (t : (Y ⊗ A : Rep k G)) :
    LinearMap.lTensor Y.V r ((Y ◁ f).hom t) = t := by sorry
