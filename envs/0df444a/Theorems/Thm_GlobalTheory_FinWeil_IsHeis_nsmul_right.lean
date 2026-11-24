-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_IsHeis_nsmul_right
-- name    : GlobalTheory.FinWeil.IsHeis.nsmul_right
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:39.128977+00:00
-- url     : https://prove2.me/theorems/4b33860f-4d29-491a-aed7-84b3c5c15000
-- title:
--   Is Heis: nsmul right
-- statement:
--   The Is Heis construction uses the nsmul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L83-L86

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
open GlobalTheory.FinWeil.IsHeis
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W)
include h

theorem GlobalTheory.FinWeil.IsHeis.nsmul_right (n : ℕ) (x y : X) : γ x (n • y) = γ x y ^ n := by sorry
