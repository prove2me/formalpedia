-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_integer_subgroup_torsion
-- name    : GroundTheory.ProfCoh.integer_subgroup_torsion
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:26.544518+00:00
-- url     : https://prove2.me/theorems/16f053bb-7c00-4d73-ad89-8e2c66180d7f
-- title:
--   Prof Coh: integer subgroup torsion
-- statement:
--   The Prof Coh construction uses the integer subgroup torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L173-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L173-L179

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
variable {F : Type*} [Field F] [ValuativeRel F]

theorem GroundTheory.ProfCoh.integer_subgroup_torsion {m : ℕ} (hm : (m : F) ≠ 0) (H : AddSubgroup 𝒪[F]) (a : H)
    (ha : m • a = 0) : a = 0 := by sorry
