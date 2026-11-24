-- Prove2me | Theorems.Thm_GlobalTheory_MinpolyHeightCount_abs_coeff_minpoly_int_le
-- name    : GlobalTheory.MinpolyHeightCount.abs_coeff_minpoly_int_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:42.054686+00:00
-- url     : https://prove2.me/theorems/75628f52-3924-4164-876e-d2f030f5b52f
-- title:
--   Minpoly Height Count: abs coeff minpoly int le
-- statement:
--   The Minpoly Height Count construction uses the abs coeff minpoly int le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L57-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable (K : Type) [Field K] [NumberField K]

theorem GlobalTheory.MinpolyHeightCount.abs_coeff_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) {R : ℝ}
    (h : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R) (i : ℕ) :
    (|(minpoly ℤ x).coeff i| : ℝ) ≤ max R 1 ^ Module.finrank ℚ K *
      (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) := by sorry
