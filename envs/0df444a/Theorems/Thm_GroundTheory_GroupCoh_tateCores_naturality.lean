-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCores_naturality
-- name    : GroundTheory.GroupCoh.tateCores_naturality
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:03.815613+00:00
-- url     : https://prove2.me/theorems/635e6eb7-672a-489b-9ec1-f1bb0aa7c78b
-- title:
--   Group Coh: tate Cores naturality
-- statement:
--   The Group Coh construction uses the tate Cores naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L85-L88

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

theorem GroundTheory.GroupCoh.tateCores_naturality {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℤ) :
    (resFunctor S.subtype ⋙ tateCohomologyFunctor n).map f ≫ (tateCores S n).app B =
      (tateCores S n).app A ≫ (tateCohomologyFunctor n).map f := by sorry
