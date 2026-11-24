-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_swap
-- name    : GlobalTheory.HCA.dw_swap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:59:28.926337+00:00
-- url     : https://prove2.me/theorems/f585035a-1240-42ba-81f4-8fbeb1c21ca3
-- title:
--   HCA: dw swap
-- statement:
--   The HCA construction uses the dw swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L66-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.dw_swap {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (a b : Fin d) {g : E d → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : Set.EqOn (dw [a, b] g) (dw [b, a] g) U := by sorry
