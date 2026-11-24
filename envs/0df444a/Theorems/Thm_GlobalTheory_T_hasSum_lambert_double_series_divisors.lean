-- Prove2me | Theorems.Thm_GlobalTheory_T_hasSum_lambert_double_series_divisors
-- name    : GlobalTheory.T.hasSum_lambert_double_series_divisors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:43:54.629063+00:00
-- url     : https://prove2.me/theorems/30ee4760-d45d-4a05-8cbb-9654dc514022
-- title:
--   T: has Sum lambert double series divisors
-- statement:
--   The T construction uses the has Sum lambert double series divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumLambertDoubleSeriesDivisorsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumLambertDoubleSeriesDivisorsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumLambertDoubleSeriesDivisors
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumLambertDoubleSeriesDivisorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hasSum_lambert_double_series_divisors : ∀ (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ), ‖Q‖ < 1 → (∀ d m, ‖c d m‖ ≤ 1) → HasSum (fun k : ℕ => (∑ m ∈ k.divisors, (m : ℂ) ^ e * c (k / m) m) * Q ^ k) (∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c d m * Q ^ ((d : ℕ) * (m : ℕ))) := by sorry
