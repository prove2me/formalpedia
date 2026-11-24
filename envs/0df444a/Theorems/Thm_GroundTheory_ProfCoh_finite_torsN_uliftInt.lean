-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_torsN_uliftInt
-- name    : GroundTheory.ProfCoh.finite_torsN_uliftInt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:13.91789+00:00
-- url     : https://prove2.me/theorems/68feb62f-21ae-43e0-b5b1-be2f5eacd6b9
-- title:
--   Prof Coh: finite tors N ulift Int
-- statement:
--   The Prof Coh construction uses the finite tors N ulift Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L72-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L72-L83

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10

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

theorem GroundTheory.ProfCoh.finite_torsN_uliftInt (l : ℕ) [NeZero l] : Finite (TorsN (ULift.{u} ℤ) l) := by sorry
