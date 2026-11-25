-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_toAdditive_subtype_injective
-- name    : GroundTheory.ProfCoh.toAdditive_subtype_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:55.122852+00:00
-- url     : https://prove2.me/theorems/a89da554-4f62-45a6-87a0-0e3751997c3d
-- title:
--   Prof Coh: to Additive subtype injective
-- statement:
--   The Prof Coh construction uses the to Additive subtype injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L149-L151

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing

theorem GroundTheory.ProfCoh.toAdditive_subtype_injective {G : Type*} [CommGroup G] (H : Subgroup G) :
    Function.Injective H.subtype.toAdditive := by sorry
