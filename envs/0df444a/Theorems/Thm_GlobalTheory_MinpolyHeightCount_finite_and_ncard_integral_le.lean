-- Prove2me | Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_integral_le
-- name    : GlobalTheory.MinpolyHeightCount.finite_and_ncard_integral_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:38.730951+00:00
-- url     : https://prove2.me/theorems/81986ea5-6b10-44a3-a54c-b06653ebf605
-- title:
--   Minpoly Height Count: finite and ncard integral le
-- statement:
--   The Minpoly Height Count construction uses the finite and ncard integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L65-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L65-L121

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

theorem GlobalTheory.MinpolyHeightCount.finite_and_ncard_integral_le (R : ℝ) :
    {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.Finite ∧
    (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ) ≤
      Module.finrank ℚ K * (2 * (max R 1 ^ Module.finrank ℚ K *
        (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2)) + 3) ^
          (Module.finrank ℚ K + 1) := by sorry
