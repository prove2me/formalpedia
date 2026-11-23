-- Prove2me | Theorems.Thm_GlobalTheory_FinWeil_IsHeis_neg_comp
-- name    : GlobalTheory.FinWeil.IsHeis.neg_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:42.12062+00:00
-- url     : https://prove2.me/theorems/b9484118-0c31-47a3-88d4-4dfcf1ae31e7
-- title:
--   Is Heis: neg comp
-- statement:
--   The Is Heis construction uses the neg comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean#L100-L101

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

theorem GlobalTheory.FinWeil.IsHeis.neg_comp (x : X) (v : M) : W (-x) (W x v) = γ (w • -x) x • v := by sorry
