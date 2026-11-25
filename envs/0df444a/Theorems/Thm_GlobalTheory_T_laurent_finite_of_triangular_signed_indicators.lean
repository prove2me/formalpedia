-- Prove2me | Theorems.Thm_GlobalTheory_T_laurent_finite_of_triangular_signed_indicators
-- name    : GlobalTheory.T.laurent_finite_of_triangular_signed_indicators
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:51.770536+00:00
-- url     : https://prove2.me/theorems/e9a6dea4-4963-44b7-9c75-168b5df8e339
-- title:
--   T: laurent finite of triangular signed indicators
-- statement:
--   The T construction uses the laurent finite of triangular signed indicators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicatorsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LaurentFiniteOfTriangularSignedIndicatorsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicators
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LaurentFiniteOfTriangularSignedIndicatorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.laurent_finite_of_triangular_signed_indicators : ∀ (m : ℕ) (B : Subalgebra ℂ (AddMonoidAlgebra ℂ (Fin m → ℤ))), (∀ ε : Fin m → ℤ, (∀ i, |ε i| ≤ 1) → ∃ s ∈ B, s.coeff ε ≠ 0 ∧ ∀ κ, s.coeff κ ≠ 0 → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i|) → Module.Finite B (AddMonoidAlgebra ℂ (Fin m → ℤ)) := by sorry
