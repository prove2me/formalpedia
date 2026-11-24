-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_exists_char_of_mul_on_cone
-- name    : GlobalTheory.CompanionTheory.StrictCone.exists_char_of_mul_on_cone
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:15:01.00423+00:00
-- url     : https://prove2.me/theorems/3edf126f-675d-47f3-b424-58b74e82029c
-- title:
--   Strict Cone: exists char of mul on cone
-- statement:
--   The Strict Cone construction uses the exists char of mul on cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L5-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L5-L55

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone

theorem GlobalTheory.CompanionTheory.StrictCone.exists_char_of_mul_on_cone {G : Type*} [AddCommGroup G] (S : Set G)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (f : G → ℂ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ S) (hne : f s₀ ≠ 0)
    (arch : ∀ g : G, ∃ k : ℕ, 0 < k ∧ k • s₀ + g ∈ S) :
    ∃ φ : G → ℂˣ, (∀ g h, φ (g + h) = φ g * φ h) ∧ ∀ s ∈ S, f s = (φ s : ℂ) := by sorry
