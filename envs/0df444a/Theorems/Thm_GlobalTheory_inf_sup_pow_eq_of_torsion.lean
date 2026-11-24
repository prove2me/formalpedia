-- Prove2me | Theorems.Thm_GlobalTheory_inf_sup_pow_eq_of_torsion
-- name    : GlobalTheory.inf_sup_pow_eq_of_torsion
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:55:26.14781+00:00
-- url     : https://prove2.me/theorems/e3f49074-1829-4477-8968-8947e1a7419a
-- title:
--   Global Theory: inf sup pow eq of torsion
-- statement:
--   The Global Theory construction uses the inf sup pow eq of torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InfSupPowEqOfTorsionArtinRees.lean#L5-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InfSupPowEqOfTorsionArtinRees.lean#L5-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfSupPowEqOfTorsionArtinRees
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.inf_sup_pow_eq_of_torsion : ∀ (B : Type) [CommRing B] [IsNoetherianRing B]
    (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by sorry
