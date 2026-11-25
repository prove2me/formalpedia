-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_moduleHom_smul
-- name    : GroundTheory.GroupCoh.moduleHom_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:21.733625+00:00
-- url     : https://prove2.me/theorems/7a2935ad-cc5a-4bbc-addd-bc9fd7b5a411
-- title:
--   Group Coh: module Hom smul
-- statement:
--   The Group Coh construction uses the module Hom smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L250-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L250-L252

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]

theorem GroundTheory.GroupCoh.moduleHom_smul {M N : ModuleCat.{u} k} (f : M ⟶ N) (c : k) (y : M) :
    f.hom (c • y) = c • f.hom y := by sorry
