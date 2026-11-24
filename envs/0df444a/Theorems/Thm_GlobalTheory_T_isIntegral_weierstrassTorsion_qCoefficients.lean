-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_weierstrassTorsion_qCoefficients
-- name    : GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:12:17.515602+00:00
-- url     : https://prove2.me/theorems/e078da3d-60a5-4dc3-911b-ac2c17495e3f
-- title:
--   T: is Integral weierstrass Torsion q Coefficients
-- statement:
--   The T construction uses the is Integral weierstrass Torsion q Coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralWeierstrassTorsionQCoefficientsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralWeierstrassTorsionQCoefficientsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralWeierstrassTorsionQCoefficients
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralWeierstrassTorsionQCoefficientsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ), 0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * cB N x k) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * cP N x k) ∧ IsIntegral ℤ (12 * cG N k) := by sorry
