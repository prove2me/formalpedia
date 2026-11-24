-- Prove2me | Theorems.Thm_GlobalTheory_adic_coeffs_tendsto_zero
-- name    : GlobalTheory.adic_coeffs_tendsto_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:09.874669+00:00
-- url     : https://prove2.me/theorems/b0a1837e-17f3-4c5e-bff7-8ada081ace80
-- title:
--   Global Theory: adic coeffs tendsto zero
-- statement:
--   The Global Theory construction uses the adic coeffs tendsto zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCoeffsTendstoZero.lean#L6-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCoeffsTendstoZero.lean#L6-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCoeffsTendstoZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.adic_coeffs_tendsto_zero :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by sorry
