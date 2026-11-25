-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_freeLift_cochainsMap_subtype
-- name    : GroundTheory.GroupCoh.freeLift_cochainsMap_subtype
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:48.28352+00:00
-- url     : https://prove2.me/theorems/bad6c696-ed1c-5b0f-bce3-2707149a10fb
-- title:
--   Group Coh: free Lift cochains Map subtype
-- statement:
--   The Group Coh construction uses the free Lift cochains Map subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L103-L111

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
set_option backward.isDefEq.respectTransparency false

theorem GroundTheory.GroupCoh.freeLift_cochainsMap_subtype (A : Rep.{u} k G) (n : ℕ) (y : (Fin n → G) → A) :
    freeLift k S (res S.subtype A) (((cochainsMap S.subtype (𝟙 (res S.subtype A))).f n).hom y) =
      barInclF S n ≫ (resFunctor S.subtype).map (freeLift k G A y) := by sorry
