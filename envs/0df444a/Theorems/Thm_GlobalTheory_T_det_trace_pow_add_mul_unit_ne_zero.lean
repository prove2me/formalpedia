-- Prove2me | Theorems.Thm_GlobalTheory_T_det_trace_pow_add_mul_unit_ne_zero
-- name    : GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:12.802496+00:00
-- url     : https://prove2.me/theorems/40158ca9-0624-5e4c-87ae-779e81690b1e
-- title:
--   T: det trace pow add mul unit ne zero
-- statement:
--   The T construction uses the det trace pow add mul unit ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetTracePowAddMulUnitNeZeroStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetTracePowAddMulUnitNeZeroStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTracePowAddMulUnitNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTracePowAddMulUnitNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.det_trace_pow_add_mul_unit_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u → (Matrix.of fun k l : Fin (Module.finrank K.E B.A) => Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by sorry
