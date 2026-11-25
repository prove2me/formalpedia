-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_moduleIso_hom_injective
-- name    : GroundTheory.GroupCoh.moduleIso_hom_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:39:38.180822+00:00
-- url     : https://prove2.me/theorems/2281a674-8a26-4f48-a615-d9f41533d418
-- title:
--   Group Coh: module Iso hom injective
-- statement:
--   The Group Coh construction uses the module Iso hom injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L257-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L257-L260

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

theorem GroundTheory.GroupCoh.moduleIso_hom_injective {M N : ModuleCat.{u} k} (e : M ≅ N) : Function.Injective e.hom.hom := by sorry
