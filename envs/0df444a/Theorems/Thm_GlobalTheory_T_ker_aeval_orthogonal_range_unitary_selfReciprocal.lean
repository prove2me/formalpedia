-- Prove2me | Theorems.Thm_GlobalTheory_T_ker_aeval_orthogonal_range_unitary_selfReciprocal
-- name    : GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:23.772889+00:00
-- url     : https://prove2.me/theorems/46917f0e-3959-584e-9d83-7fde7e09c3f5
-- title:
--   T: ker aeval orthogonal range unitary self Reciprocal
-- statement:
--   The T construction uses the ker aeval orthogonal range unitary self Reciprocal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerAevalOrthogonalRangeUnitarySelfReciprocalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerAevalOrthogonalRangeUnitarySelfReciprocalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalOrthogonalRangeUnitarySelfReciprocal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalOrthogonalRangeUnitarySelfReciprocalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal : ∀ {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K), (γ.map σ)ᵀ * γ = 1 → ∀ (Q : K[X]), C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse → ∀ (x z : Fin n → K), aeval γ Q *ᵥ x = 0 → ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 := by sorry
