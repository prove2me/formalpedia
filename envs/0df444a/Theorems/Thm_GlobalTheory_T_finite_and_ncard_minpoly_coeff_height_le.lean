-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_and_ncard_minpoly_coeff_height_le
-- name    : GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:36.906682+00:00
-- url     : https://prove2.me/theorems/4dc70dfa-477e-4231-be22-3ce3cffcb13d
-- title:
--   T: finite and ncard minpoly coeff height le
-- statement:
--   The T construction uses the finite and ncard minpoly coeff height le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLeStatement
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

theorem GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by sorry
