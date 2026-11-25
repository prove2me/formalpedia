-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_modNEquivOfSurjective_mk
-- name    : GroundTheory.ProfCoh.modNEquivOfSurjective_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:35.884476+00:00
-- url     : https://prove2.me/theorems/ccc44b46-fad0-4838-acbd-50e1478bb8bd
-- title:
--   Prof Coh: mod NEquiv Of Surjective mk
-- statement:
--   The Prof Coh construction uses the mod NEquiv Of Surjective mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L40-L43

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
variable {n : ℕ} {A X : Type*} [AddCommGroup A] [AddCommGroup X] [Module (ZMod n) X]

theorem GroundTheory.ProfCoh.modNEquivOfSurjective_mk (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n)) (a : A) :
    modNEquivOfSurjective φ hs hker (Submodule.Quotient.mk a) = φ a := by sorry
