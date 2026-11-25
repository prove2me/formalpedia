-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_invariants_comp_of_surjective
-- name    : GroundTheory.ProfCoh.invariants_comp_of_surjective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:37.998311+00:00
-- url     : https://prove2.me/theorems/09eca1e2-c976-450e-bb6b-ee7c4e19b59e
-- title:
--   Prof Coh: invariants comp of surjective
-- statement:
--   The Prof Coh construction uses the invariants comp of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/CoprimeRegular.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/CoprimeRegular.lean#L103-L108

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_CoprimeRegular
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
open Representation TensorProduct
variable {k Γ₁ Γ₂ X : Type*} [CommRing k] [Group Γ₁] [Group Γ₂] [AddCommGroup X] [Module k X]

theorem GroundTheory.ProfCoh.invariants_comp_of_surjective (ρ : Representation k Γ₁ X) (e : Γ₂ →* Γ₁)
    (he : Function.Surjective e) :
    Representation.invariants (ρ.comp e) = ρ.invariants := by sorry
