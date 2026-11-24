-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_quotient_range_toAdditive
-- name    : GroundTheory.ProfCoh.finite_quotient_range_toAdditive
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:56.111767+00:00
-- url     : https://prove2.me/theorems/85c66c09-f73f-45f6-a066-084b32caee0d
-- title:
--   Prof Coh: finite quotient range to Additive
-- statement:
--   The Prof Coh construction uses the finite quotient range to Additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L133-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L133-L147

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

theorem GroundTheory.ProfCoh.finite_quotient_range_toAdditive {G : Type*} [CommGroup G] (H : Subgroup G)
    [H.FiniteIndex] : Finite (Additive G ⧸ (H.subtype.toAdditive).range) := by sorry
