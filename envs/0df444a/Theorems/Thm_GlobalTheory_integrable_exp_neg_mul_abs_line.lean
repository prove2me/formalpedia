-- Prove2me | Theorems.Thm_GlobalTheory_integrable_exp_neg_mul_abs_line
-- name    : GlobalTheory.integrable_exp_neg_mul_abs_line
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:25.821703+00:00
-- url     : https://prove2.me/theorems/17112d84-598d-44ad-909c-34a1242c19fa
-- title:
--   Global Theory: integrable exp neg mul abs line
-- statement:
--   The Global Theory construction uses the integrable exp neg mul abs line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EqZeroOfExpDecayOfFourierEqZeroOnHalfLine.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EqZeroOfExpDecayOfFourierEqZeroOnHalfLine.lean#L10-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegrableExpNegMulAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EqZeroOfExpDecayOfFourierEqZeroOnHalfLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology FourierTransform
open GlobalTheory

theorem GlobalTheory.integrable_exp_neg_mul_abs_line {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.exp (-(c * |s|))) := by sorry
