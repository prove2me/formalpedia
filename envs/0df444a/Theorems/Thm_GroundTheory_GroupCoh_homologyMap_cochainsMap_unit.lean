-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_homologyMap_cochainsMap_unit
-- name    : GroundTheory.GroupCoh.homologyMap_cochainsMap_unit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:35:53.400473+00:00
-- url     : https://prove2.me/theorems/a485e8a9-2201-4f4a-8a2f-f6333f0d648a
-- title:
--   Group Coh: homology Map cochains Map unit
-- statement:
--   The Group Coh construction uses the homology Map cochains Map unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L141-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L141-L178

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

theorem GroundTheory.GroupCoh.homologyMap_cochainsMap_unit (A : Rep.{u} k G) (n : ℕ) :
    HomologicalComplex.homologyMap (cochainsMap (MonoidHom.id G)
        ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A)) n =
      groupCohomology.map S.subtype (𝟙 (res S.subtype A)) n ≫
        HomologicalComplex.homologyMap (shapiroCochainsHomotopyEquiv S (res S.subtype A)).hom n := by sorry
