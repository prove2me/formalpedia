-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCoindIso_inv_tateZeroClass
-- name    : GroundTheory.GroupCoh.tateCoindIso_inv_tateZeroClass
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:03:07.007246+00:00
-- url     : https://prove2.me/theorems/98a5032e-bbe0-4b85-a2f0-6ef4690fb4aa
-- title:
--   Group Coh: tate Coind Iso inv tate Zero Class
-- statement:
--   The Group Coh construction uses the tate Coind Iso inv tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L101-L105

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
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
variable [Fintype G] [Fintype S]

theorem GroundTheory.GroupCoh.tateCoindIso_inv_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (tateCoindIso S B 0).inv.hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) := by sorry
