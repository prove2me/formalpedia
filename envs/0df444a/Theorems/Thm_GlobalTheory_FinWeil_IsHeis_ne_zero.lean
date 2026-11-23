-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero
-- name    : GlobalTheory.FinWeil.IsHeis.ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:19.192947+00:00
-- url     : https://prove2.me/theorems/32b330cc-6373-4ed9-aeae-ef59d9b346c3
-- title:
--   Is Heis: ne zero
-- statement:
--   The Is Heis construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L52-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L52-L52

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

theorem GlobalTheory.FinWeil.IsHeis.ne_zero (x y : X) : γ x y ≠ 0 := by sorry
