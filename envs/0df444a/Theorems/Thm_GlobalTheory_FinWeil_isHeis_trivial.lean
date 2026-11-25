-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_isHeis_trivial
-- name    : GlobalTheory.FinWeil.isHeis_trivial
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:39.55805+00:00
-- url     : https://prove2.me/theorems/0c35df14-863d-5a54-9405-e48d11144cbc
-- title:
--   Fin Weil: is Heis trivial
-- statement:
--   The Fin Weil construction uses the is Heis trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L105-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L105-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.FinWeil.isHeis_trivial (σ : R →+* R) (w : R) (h1 : ∀ r, σ (σ r) = r) (h2 : w + σ w = 1) :
    IsHeis σ w (fun _ _ : X => (1 : ℂ)) (fun _ => (LinearMap.id : M →ₗ[ℂ] M)) := by sorry
