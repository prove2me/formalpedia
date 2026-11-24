-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_abs_pow_mul_exp_le
-- name    : GlobalTheory.LipschitzTR.abs_pow_mul_exp_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:43.340659+00:00
-- url     : https://prove2.me/theorems/eda21e58-f7bc-4132-9238-212aecbccd29
-- title:
--   Lipschitz TR: abs pow mul exp le
-- statement:
--   The Lipschitz TR construction uses the abs pow mul exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousIsBigORpowLipschitzProductKernel.lean#L38-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousIsBigORpowLipschitzProductKernel.lean#L38-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR

theorem GlobalTheory.LipschitzTR.abs_pow_mul_exp_le (n : ℕ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t| ^ n * Real.exp (-a * |t|) ≤ (n.factorial * (2 / a) ^ n) * Real.exp (-(a / 2) * |t|) := by sorry
