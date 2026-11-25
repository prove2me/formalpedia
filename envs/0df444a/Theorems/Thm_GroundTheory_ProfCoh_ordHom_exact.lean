-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_ordHom_exact
-- name    : GroundTheory.ProfCoh.ordHom_exact
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:50:53.956271+00:00
-- url     : https://prove2.me/theorems/70d41c7c-7a2f-45b9-ac07-4241a8ea1dfa
-- title:
--   Prof Coh: ord Hom exact
-- statement:
--   The Prof Coh construction uses the ord Hom exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L115-L127

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
variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}

theorem GroundTheory.ProfCoh.ordHom_exact : Function.Exact (unitsIncl F).toAdditive (ordHom F) := by sorry
