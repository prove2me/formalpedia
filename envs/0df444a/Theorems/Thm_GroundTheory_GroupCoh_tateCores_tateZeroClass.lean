-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCores_tateZeroClass
-- name    : GroundTheory.GroupCoh.tateCores_tateZeroClass
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:02:17.495564+00:00
-- url     : https://prove2.me/theorems/bfd670f3-7622-5b46-ab4c-08b69a7b1f36
-- title:
--   Group Coh: tate Cores tate Zero Class
-- statement:
--   The Group Coh construction uses the tate Cores tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L143-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L143-L151

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
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
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

theorem GroundTheory.GroupCoh.tateCores_tateZeroClass (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((tateCores S 0).app A).hom (tateZeroClass (res S.subtype A) y) =
      tateZeroClass A (transferInv S y) := by sorry
