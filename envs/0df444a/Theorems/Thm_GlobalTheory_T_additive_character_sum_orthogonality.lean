-- Prove2me | Theorems.Thm_GlobalTheory_T_additive_character_sum_orthogonality
-- name    : GlobalTheory.T.additive_character_sum_orthogonality
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:15.510195+00:00
-- url     : https://prove2.me/theorems/6e9e2037-f8fc-4752-a647-35379a52590e
-- title:
--   T: additive character sum orthogonality
-- statement:
--   The T construction uses the additive character sum orthogonality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AdditiveCharacterSumOrthogonalityStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AdditiveCharacterSumOrthogonalityStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AdditiveCharacterSumOrthogonality
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AdditiveCharacterSumOrthogonalityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.additive_character_sum_orthogonality : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ), ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by sorry
