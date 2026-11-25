-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateRes_naturality
-- name    : GroundTheory.GroupCoh.tateRes_naturality
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:58:48.28632+00:00
-- url     : https://prove2.me/theorems/9e6cdeec-5b5b-5bed-9bc7-af35311e7d7c
-- title:
--   Group Coh: tate Res naturality
-- statement:
--   The Group Coh construction uses the tate Res naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L37-L40

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateShapiro
import Definitions.Def_GroundTheory_TateCohomology_ResCores
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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

theorem GroundTheory.GroupCoh.tateRes_naturality {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℤ) :
    (tateCohomologyFunctor n).map f ≫ (tateRes S n).app B =
      (tateRes S n).app A ≫ (resFunctor S.subtype ⋙ tateCohomologyFunctor n).map f := by sorry
