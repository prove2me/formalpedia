-- Prove2me | Theorems.Thm_GlobalTheory_T_index_squares_le_two_mul_units_squares
-- name    : GlobalTheory.T.index_squares_le_two_mul_units_squares
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:26.144801+00:00
-- url     : https://prove2.me/theorems/f47484bf-9865-4bb2-b2e0-b40e2fb42600
-- title:
--   T: index squares le two mul units squares
-- statement:
--   The T construction uses the index squares le two mul units squares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSquaresLeTwoMulUnitsSquaresStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSquaresLeTwoMulUnitsSquaresStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquares
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquaresStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.index_squares_le_two_mul_units_squares : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K), w π = WithZero.exp (-1) → (sqs (hiUnits w 0)).relIndex (hiUnits w 0) ≠ 0 → (sqs (⊤ : Subgroup Kˣ)).index ≠ 0 ∧ (sqs (⊤ : Subgroup Kˣ)).index ≤ 2 * (sqs (hiUnits w 0)).relIndex (hiUnits w 0) := by sorry
