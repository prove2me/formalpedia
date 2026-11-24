-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_isIntegral_coefficients
-- name    : GlobalTheory.WpFam.isIntegral_coefficients
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:07.464834+00:00
-- url     : https://prove2.me/theorems/d4c15a69-9920-47d6-8eb4-60f1309f1998
-- title:
--   Wp Fam: is Integral coefficients
-- statement:
--   The Wp Fam construction uses the is Integral coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralWeierstrassTorsionQCoefficients.lean#L37-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralWeierstrassTorsionQCoefficients.lean#L37-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootOfUnityExpZModAdditiveCharacterProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralWeierstrassTorsionQCoefficients
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
open GlobalTheory GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate

theorem GlobalTheory.WpFam.isIntegral_coefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ),
    0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cB N x k) ∧
      IsIntegral ℤ ((M : ℂ) ^ 3 * _root_.GlobalTheory.WpFam.cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * _root_.GlobalTheory.WpFam.cP N x k) ∧
      IsIntegral ℤ (12 * _root_.GlobalTheory.WpFam.cG N k) := by sorry
