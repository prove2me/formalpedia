-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_HessFrame_cHess_log_sum_normSq_eq
-- name    : GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:40:37.739073+00:00
-- url     : https://prove2.me/theorems/3abd9d5b-b825-49e0-bb9a-b98a8e1b1601
-- title:
--   Hess Frame: c Hess log sum norm Sq eq
-- statement:
--   The Hess Frame construction uses the c Hess log sum norm Sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComplexHessianLogDehomogenise.lean#L19-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ComplexHessianLogDehomogenise.lean#L19-L56

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpbHessAtAddConst
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogenise
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.HessFrame

theorem GlobalTheory.CompanionTheory.FSCrofton.HessFrame.cHess_log_sum_normSq_eq (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α)
    (U : Set (V d)) (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (h0 : ∀ z ∈ U, b j₀ z ≠ 0) : ∀ z ∈ U,
    cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z =
      cHess d (fun v => ((Real.log (1 + ∑ j : {j : α // j ≠ j₀}, ‖b j.1 v / b j₀ v‖ ^ 2) : ℝ) : ℂ))
        z := by sorry
