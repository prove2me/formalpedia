-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCoindIso_inv
-- name    : GroundTheory.GroupCoh.tateCoindIso_inv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:03:39.555257+00:00
-- url     : https://prove2.me/theorems/0589d2e9-54e9-45bf-acf1-459e1f3f2016
-- title:
--   Group Coh: tate Coind Iso inv
-- statement:
--   The Group Coh construction uses the tate Coind Iso inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L90-L93

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

theorem GroundTheory.GroupCoh.tateCoindIso_inv (B : Rep.{u} k S) (n : ℤ) :
    (tateCoindIso S B n).inv = HomologicalComplex.homologyMap (tateShapiroMap S B) n := by sorry
