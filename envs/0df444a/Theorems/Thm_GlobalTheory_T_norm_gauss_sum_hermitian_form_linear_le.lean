-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_gauss_sum_hermitian_form_linear_le
-- name    : GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:18.458874+00:00
-- url     : https://prove2.me/theorems/c7a16731-7f50-48c7-acc9-9407bbdb0217
-- title:
--   T: norm gauss sum hermitian form linear le
-- statement:
--   The T construction uses the norm gauss sum hermitian form linear le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormGaussSumHermitianFormLinearLeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormGaussSumHermitianFormLinearLeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (n : ℕ) (a : B), IsUnit (a + c a) → ∀ (v : Fin n → B), ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by sorry
