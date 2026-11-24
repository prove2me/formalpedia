-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTate_comp_sub_mem
-- name    : GlobalTheory.HeckeTate.comp_sub_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:59.051141+00:00
-- url     : https://prove2.me/theorems/2da2a163-88d9-4f0f-9224-fab9c19912bb
-- title:
--   Hecke Tate: comp sub mem
-- statement:
--   The Hecke Tate construction uses the comp sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L103-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdMulOfIdem.lean#L103-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

theorem GlobalTheory.HeckeTate.comp_sub_mem {N : R} (u₁ u₂ u₃ : M →ₗ[R] M') (w₁ w₂ w₃ : M' →ₗ[R] M) {t₁ t₂ t₃ a₁ a₂ a₃ b₁ b₂ b₃ : R}
    (h₁ : ∀ x, w₁ (u₁ x) = t₁ • x) (h₂ : ∀ x, w₂ (u₂ x) = t₂ • x) (h₃ : ∀ x, w₃ (u₃ x) = t₃ • x)
    (h12 : N ∣ a₁ * b₂) (h13 : N ∣ a₁ * b₃) (h21 : N ∣ a₂ * b₁) (h23 : N ∣ a₂ * b₃)
    (h31 : N ∣ a₃ * b₁) (h32 : N ∣ a₃ * b₂)
    (h : N ∣ a₁ * b₁ * t₁ + a₂ * b₂ * t₂ + a₃ * b₃ * t₃ - 1) (x : M) :
    (b₁ • w₁ + b₂ • w₂ + b₃ • w₃) ((a₁ • u₁ + a₂ • u₂ + a₃ • u₃) x) - x ∈ mults M N := by sorry
