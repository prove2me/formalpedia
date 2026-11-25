-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateRes_tateZeroClass
-- name    : GroundTheory.GroupCoh.tateRes_tateZeroClass
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:39.749389+00:00
-- url     : https://prove2.me/theorems/b589b734-97b2-454f-85fe-e90ea56c4475
-- title:
--   Group Coh: tate Res tate Zero Class
-- statement:
--   The Group Coh construction uses the tate Res tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L113-L123

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

theorem GroundTheory.GroupCoh.tateRes_tateZeroClass (A : Rep.{u} k G) (x : A.ρ.invariants) :
    ((tateRes S 0).app A).hom (tateZeroClass A x) =
      tateZeroClass (res S.subtype A) (invariantsRes S.subtype x) := by sorry
