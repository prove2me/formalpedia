-- Prove2me | Theorems.Thm_GlobalTheory_KerPerp_nil_eq_zero
-- name    : GlobalTheory.KerPerp.nil_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:14.644194+00:00
-- url     : https://prove2.me/theorems/eec40ea2-7f91-49ac-bf0c-4a4de06ac842
-- title:
--   Ker Perp: nil eq zero
-- statement:
--   The Ker Perp construction uses the nil eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L121-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.KerPerp
variable {O L Y : Type*} [Ring O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {bar : O → O} {EF : LinearMap.BilinForm ℤ L}
variable {hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (bar a • x')} {y : L →ₗ[O] Y}
variable (hadj)
variable {be : LinearMap.BilinForm ℤ Y}
variable {hadj}
variable {nn : L → L}

theorem GlobalTheory.KerPerp.nil_eq_zero (hi : Function.Injective EF) (h : ∀ a b, -EF (nn a) b = be (y a) (y b)) {a : L}
    (ha : y a = 0) : nn a = 0 := by sorry
