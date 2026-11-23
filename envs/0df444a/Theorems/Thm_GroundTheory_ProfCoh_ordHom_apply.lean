-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_ordHom_apply
-- name    : GroundTheory.ProfCoh.ordHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:58.842187+00:00
-- url     : https://prove2.me/theorems/fc07099a-2905-4ef8-a7a3-e594f47218fc
-- title:
--   Prof Coh: ord Hom apply
-- statement:
--   The Prof Coh construction uses the ord Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L102-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L102-L103

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

theorem GroundTheory.ProfCoh.ordHom_apply (x : Additive Fˣ) : ordHom F x = ULift.up (ord ((x.toMul : Fˣ) : F)) := by sorry
