-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_Involution_bijective_flip_of_pairing_eq
-- name    : GroundTheory.ProfCoh.Involution.bijective_flip_of_pairing_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:44.119536+00:00
-- url     : https://prove2.me/theorems/640bf988-373e-4c1e-ba91-98a8016e9346
-- title:
--   Involution: bijective flip of pairing eq
-- statement:
--   The Involution construction uses the bijective flip of pairing eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/RealPlaces/InvolutionDuality.lean#L228-L231

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality
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
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
variable {σ : M →+ M}
variable {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']

theorem GroundTheory.ProfCoh.Involution.bijective_flip_of_pairing_eq (P : X →+ Y →+ QZ) (Q : X' →+ Y' →+ QZ) (e : X' ≃+ X)
    (e' : Y' ≃+ Y) (h : ∀ x y, P (e x) (e' y) = Q x y) (hQ : Function.Bijective Q.flip) :
    Function.Bijective P.flip := by sorry
