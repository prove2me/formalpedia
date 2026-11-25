-- Prove2me | Theorems.Thm_GlobalTheory_T_integer_coordinates_bound
-- name    : GlobalTheory.T.integer_coordinates_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:33:40.691261+00:00
-- url     : https://prove2.me/theorems/a8093f73-7ed5-53e1-9981-451237631cc4
-- title:
--   T: integer coordinates bound
-- statement:
--   The T construction uses the integer coordinates bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegerCoordinatesBoundStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegerCoordinatesBoundStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegerCoordinatesBound
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegerCoordinatesBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.integer_coordinates_bound : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (τ : I → (E →+* ℂ)), Function.Surjective (fun i => InfinitePlace.mk (τ i)) → ∃ K : ℝ, 0 < K ∧ ∀ (e : 𝓞 E) (R : ℝ), (∀ i, ‖τ i (e : E)‖ ≤ R) → ∀ k, |(((RingOfIntegers.basis E).repr e k : ℤ) : ℝ)| ≤ K * R := by sorry
