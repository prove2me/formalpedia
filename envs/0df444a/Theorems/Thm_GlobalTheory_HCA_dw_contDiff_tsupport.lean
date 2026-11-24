-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_contDiff_tsupport
-- name    : GlobalTheory.HCA.dw_contDiff_tsupport
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:00:31.052105+00:00
-- url     : https://prove2.me/theorems/0a5410ff-dfcd-4f0b-aac3-dd119be2f6ff
-- title:
--   HCA: dw cont Diff tsupport
-- statement:
--   The HCA construction uses the dw cont Diff tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L50-L59

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

theorem GlobalTheory.HCA.dw_contDiff_tsupport {d : ℕ} (w : List (Fin d)) {φ : E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (dw w φ) ∧ tsupport (dw w φ) ⊆ tsupport φ := by sorry
