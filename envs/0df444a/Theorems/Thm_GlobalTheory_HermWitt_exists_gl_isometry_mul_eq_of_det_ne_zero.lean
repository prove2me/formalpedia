-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mul_eq_of_det_ne_zero
-- name    : GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:20:06.105451+00:00
-- url     : https://prove2.me/theorems/0cde24eb-6294-4151-b156-f32dfeb54361
-- title:
--   Herm Witt: exists gl isometry mul eq of det ne zero
-- statement:
--   The Herm Witt construction uses the exists gl isometry mul eq of det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L382-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L382-L396

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a)
    {m : Type*} [Fintype m] [DecidableEq m] {X Y : Matrix n m E}
    (hX : (Xᵀ * G * X.map c).det ≠ 0) (hXY : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : GL n E, (γ : Matrix n n E)ᵀ * G * (γ : Matrix n n E).map c = G ∧
      (γ : Matrix n n E) * X = Y := by sorry
