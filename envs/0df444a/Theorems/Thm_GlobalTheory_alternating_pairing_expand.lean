-- Prove2me | Theorems.Thm_GlobalTheory_alternating_pairing_expand
-- name    : GlobalTheory.alternating_pairing_expand
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:37.376808+00:00
-- url     : https://prove2.me/theorems/9eeb8254-3506-4b89-b48b-2f57f39a828d
-- title:
--   Global Theory: alternating pairing expand
-- statement:
--   The Global Theory construction uses the alternating pairing expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlternatingFormLatticeIntegrality.lean#L7-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlternatingFormLatticeIntegrality.lean#L7-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlternatingFormLatticeIntegrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.alternating_pairing_expand {F V : Type} [Field F] [NumberField F] [AddCommGroup V]
    [Module F V] (L : Set V)
    (hadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hsm : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (Q : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, Q x x' = -Q x' x)
    (hQadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, Q (x₁ + x₂) x' = Q x₁ x' + Q x₂ x')
    (hQsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, Q ((a : F) • x) x' = (a : F) * Q x x')
    {x x' : V} (hx : x ∈ L) (hx' : x' ∈ L) (r₀ r₁ s₀ s₁ : 𝓞 F) :
    Q ((r₀ : F) • x + (r₁ : F) • x') ((s₀ : F) • x + (s₁ : F) • x') =
      ((r₀ : F) * s₁ - (r₁ : F) * s₀) * Q x x' := by sorry
