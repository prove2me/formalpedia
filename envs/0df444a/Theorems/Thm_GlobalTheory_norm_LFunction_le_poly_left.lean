-- Prove2me | Theorems.Thm_GlobalTheory_norm_LFunction_le_poly_left
-- name    : GlobalTheory.norm_LFunction_le_poly_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:06.84835+00:00
-- url     : https://prove2.me/theorems/426a6c08-9075-4d91-a0b3-87bf368fff19
-- title:
--   Global Theory: norm LFunction le poly left
-- statement:
--   The Global Theory construction uses the norm LFunction le poly left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L269-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L269-L320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open LLeft

theorem GlobalTheory.norm_LFunction_le_poly_left :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ,
      -(7/4 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤ C * (q : ℝ) ^ 4 * (‖s‖ + 2) ^ 4 := by sorry
