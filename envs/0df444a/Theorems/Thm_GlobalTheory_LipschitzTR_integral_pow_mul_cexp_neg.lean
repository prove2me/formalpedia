-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_integral_pow_mul_cexp_neg
-- name    : GlobalTheory.LipschitzTR.integral_pow_mul_cexp_neg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:00.876908+00:00
-- url     : https://prove2.me/theorems/057387af-4747-4c91-85b9-016b4f0f05be
-- title:
--   Lipschitz TR: integral pow mul cexp neg
-- statement:
--   The Lipschitz TR construction uses the integral pow mul cexp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierLipschitzOneVariableKernelEq.lean#L36-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FourierLipschitzOneVariableKernelEq.lean#L36-L82

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierLipschitzOneVariableKernelEq
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
open Set Filter Topology

theorem GlobalTheory.LipschitzTR.integral_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by sorry
