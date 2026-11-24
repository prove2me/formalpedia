-- Prove2me | Theorems.Thm_GlobalTheory_T_continuous_isBigO_rpow_lipschitzProductKernel
-- name    : GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:03.726333+00:00
-- url     : https://prove2.me/theorems/b01b9396-e833-4073-b754-d3ed92d11aca
-- title:
--   T: continuous is Big O rpow lipschitz Product Kernel
-- statement:
--   The T construction uses the continuous is Big O rpow lipschitz Product Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousIsBigORpowLipschitzProductKernelStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousIsBigORpowLipschitzProductKernelStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernelStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by sorry
