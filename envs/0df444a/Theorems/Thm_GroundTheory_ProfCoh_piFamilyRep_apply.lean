-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_piFamilyRep_apply
-- name    : GroundTheory.ProfCoh.piFamilyRep_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:02:11.156744+00:00
-- url     : https://prove2.me/theorems/4eebf931-7b40-52cb-abe7-5153bd41b876
-- title:
--   Prof Coh: pi Family Rep apply
-- statement:
--   The Prof Coh construction uses the pi Family Rep apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinDefs.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinDefs.lean#L47-L50

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveInvariants
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ArtinDefs
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
open Representation
open scoped TensorProduct
universe u v
variable {k Γ : Type*} [CommSemiring k] [Monoid Γ]

theorem GroundTheory.ProfCoh.piFamilyRep_apply {ι : Type*} (V : ι → Type*) [∀ i, AddCommMonoid (V i)]
    [∀ i, Module k (V i)] (ρ : ∀ i, Representation k Γ (V i)) (γ : Γ) (x : ∀ i, V i) (i : ι) :
    piFamilyRep V ρ γ x i = ρ i γ (x i) := by sorry

attribute [defeq] GroundTheory.ProfCoh.piFamilyRep_apply
