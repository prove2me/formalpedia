-- Prove2me | Theorems.Thm_GlobalTheory_ShiftedTheta_shifted_theta_bound
-- name    : GlobalTheory.ShiftedTheta.shifted_theta_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:17.526683+00:00
-- url     : https://prove2.me/theorems/10065d6a-8211-48e3-8e5c-60f9c3577f4c
-- title:
--   Shifted Theta: shifted theta bound
-- statement:
--   The Shifted Theta construction uses the shifted theta bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L73-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableExpNegMulSq.lean#L73-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ShiftedTheta

theorem GlobalTheory.ShiftedTheta.shifted_theta_bound : ∀ s θ : ℝ, 0 < s → Summable (fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2))) ∧ |∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) - Real.sqrt (Real.pi / s)| ≤ Real.sqrt (Real.pi / s) * s ^ 2 := by sorry
