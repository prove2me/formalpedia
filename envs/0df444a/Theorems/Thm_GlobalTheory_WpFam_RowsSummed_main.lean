-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_RowsSummed_main
-- name    : GlobalTheory.WpFam.RowsSummed.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:42:04.695599+00:00
-- url     : https://prove2.me/theorems/c08ba001-e7fd-49f4-83d5-7c3d517a553c
-- title:
--   Rows Summed: main
-- statement:
--   The Rows Summed construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionPointRowsSumEqDivisorSeries.lean#L30-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionPointRowsSumEqDivisorSeries.lean#L30-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumLambertDoubleSeriesDivisorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumResidueClassSplitBySignStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowSumEqQExpansionSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeries
import Theorems.Thm_GlobalTheory_WpFam_AddCharZMod_main

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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.RowsSummed

theorem GlobalTheory.WpFam.RowsSummed.main : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (x : Fin 2 → ZMod N) (S : ℂ), 1 ≤ e → HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (tors N τ x + n * (τ : ℂ) + m) ^ (e + 1)) S → ∃ T : ℂ, HasSum (fun k : ℕ => cSum N e ((-1) ^ (e + 1)) x k * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T ∧ S = (if x 0 = 0 then ∑' m : ℤ, 1 / ((((x 1).val : ℂ)) / N + m) ^ (e + 1) else 0) + (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * T := by sorry
