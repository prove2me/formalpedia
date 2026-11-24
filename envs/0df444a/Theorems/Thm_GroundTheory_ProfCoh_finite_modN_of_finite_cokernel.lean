-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_finite_cokernel
-- name    : GroundTheory.ProfCoh.finite_modN_of_finite_cokernel
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:49.006455+00:00
-- url     : https://prove2.me/theorems/ca1a6376-6740-47be-b6a3-f1688a2cbc7c
-- title:
--   Prof Coh: finite mod N of finite cokernel
-- statement:
--   The Prof Coh construction uses the finite mod N of finite cokernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L153-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L153-L159

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

theorem GroundTheory.ProfCoh.finite_modN_of_finite_cokernel {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}
    (f : B →+ A) [Finite (A ⧸ f.range)] [Finite (ModN B n)] : Finite (ModN A n) := by sorry
