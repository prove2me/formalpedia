-- Prove2me | Theorems.Thm_GlobalTheory_T_finiteDimensional_of_isCompactOperator_coercive
-- name    : GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:31:09.2285+00:00
-- url     : https://prove2.me/theorems/84bc9c1e-f9ab-553a-9115-172c10fd702b
-- title:
--   T: finite Dimensional of is Compact Operator coercive
-- statement:
--   The T construction uses the finite Dimensional of is Compact Operator coercive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteDimensionalOfCompactCoerciveStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/FiniteDimensionalOfCompactCoerciveStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteDimensionalOfCompactCoercive
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_FiniteDimensionalOfCompactCoerciveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H), IsCompactOperator A → ∀ (S : Submodule ℂ H) (c : ℝ), 0 < c → (∀ u ∈ S, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) → FiniteDimensional ℂ S := by sorry
