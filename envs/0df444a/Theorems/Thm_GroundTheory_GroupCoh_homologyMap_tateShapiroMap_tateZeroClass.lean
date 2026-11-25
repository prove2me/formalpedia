-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_homologyMap_tateShapiroMap_tateZeroClass
-- name    : GroundTheory.GroupCoh.homologyMap_tateShapiroMap_tateZeroClass
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:00:56.685075+00:00
-- url     : https://prove2.me/theorems/285c8aa3-a3ba-48db-8097-525a2bcc96ba
-- title:
--   Group Coh: homology Map tate Shapiro Map tate Zero Class
-- statement:
--   The Group Coh construction uses the homology Map tate Shapiro Map tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L84-L88

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

theorem GroundTheory.GroupCoh.homologyMap_tateShapiroMap_tateZeroClass (B : Rep.{u} k S) (y : B.ρ.invariants) :
    (HomologicalComplex.homologyMap (tateShapiroMap S B) 0).hom (tateZeroClass B y) =
      tateZeroClass (coind S.subtype B) (coindConst S B y) := by sorry
