-- Prove2me | Theorems.Thm_GlobalTheory_GelfandTrick_card_pairs_le
-- name    : GlobalTheory.GelfandTrick.card_pairs_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:07:24.118564+00:00
-- url     : https://prove2.me/theorems/292a60c5-fa7c-4de4-a003-983aa950a2a5
-- title:
--   Gelfand Trick: card pairs le
-- statement:
--   The Gelfand Trick construction uses the card pairs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetOperatorsCommOfAntiInvolution.lean#L20-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetOperatorsCommOfAntiInvolution.lean#L20-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory
open GlobalTheory.GelfandTrick
variable {G : Type} [Group G]
open Classical

theorem GlobalTheory.GelfandTrick.card_pairs_le (J : Subgroup G) (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hinv : ∀ a, τ (τ a) = a) (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂)
    (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, InDoubleCoset J α γ)
    (hR' : ∀ x : G, InDoubleCoset J α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, InDoubleCoset J β γ)
    (hS' : ∀ x : G, InDoubleCoset J β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J) (c : G ⧸ J) :
    ((R ×ˢ S).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card ≤
      ((S ×ˢ R).filter (fun p => ((p.1 * p.2 : G) : G ⧸ J) = c)).card := by sorry
