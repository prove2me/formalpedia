-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_modNEquivOfSurjective_apply_modNRep
-- name    : GroundTheory.ProfCoh.modNEquivOfSurjective_apply_modNRep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:21.184488+00:00
-- url     : https://prove2.me/theorems/cc3f1ffe-1915-431d-b306-5a11126ca796
-- title:
--   Prof Coh: mod NEquiv Of Surjective apply mod NRep
-- statement:
--   The Prof Coh construction uses the mod NEquiv Of Surjective apply mod NRep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L45-L53

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

theorem GroundTheory.ProfCoh.modNEquivOfSurjective_apply_modNRep {Γ : Type*} [Group Γ] [DistribMulAction Γ A]
    (ρ : Representation (ZMod n) Γ X) (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n))
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) = ρ γ (φ a)) (γ : Γ) (x : ModN A n) :
    modNEquivOfSurjective φ hs hker (modNRep Γ A n γ x) =
      ρ γ (modNEquivOfSurjective φ hs hker x) := by sorry
