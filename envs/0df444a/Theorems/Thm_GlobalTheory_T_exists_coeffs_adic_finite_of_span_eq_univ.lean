-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_coeffs_adic_finite_of_span_eq_univ
-- name    : GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:33.874016+00:00
-- url     : https://prove2.me/theorems/72af2059-1c32-54fd-b54a-f67f9b9e7c0d
-- title:
--   T: exists coeffs adic finite of span eq univ
-- statement:
--   The T construction uses the exists coeffs adic finite of span eq univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCoeffsTendstoZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdicCoeffsTendstoZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCoeffsTendstoZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdicCoeffsTendstoZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_coeffs_adic_finite_of_span_eq_univ : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) = ⊤ → ∀ (X : Type) (z : X → M), (∀ n : ℕ, {χ | z χ ∉ (maximalIdeal R ^ n • ⊤ : Submodule R M)}.Finite) → ∃ c : X → Fin r → R, (∀ χ, z χ = ∑ j, c χ j • s j) ∧ ∀ n : ℕ, {χ | ¬ ∀ j, c χ j ∈ maximalIdeal R ^ n}.Finite := by sorry
