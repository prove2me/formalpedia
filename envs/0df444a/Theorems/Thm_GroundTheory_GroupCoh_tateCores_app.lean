-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCores_app
-- name    : GroundTheory.GroupCoh.tateCores_app
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:18.26865+00:00
-- url     : https://prove2.me/theorems/2f1df6d1-edf6-4bfb-9161-06506dd18b2a
-- title:
--   Group Coh: tate Cores app
-- statement:
--   The Group Coh construction uses the tate Cores app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCores.lean#L77-L83

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

theorem GroundTheory.GroupCoh.tateCores_app (n : ℤ) (A : Rep.{u} k G) :
    (tateCores S n).app A =
      (tateIndIso S (res S.subtype A) n).inv ≫
        (tateCohomologyFunctor n).map ((Rep.indResAdjunction.{u} k S.subtype).counit.app A) := by sorry
