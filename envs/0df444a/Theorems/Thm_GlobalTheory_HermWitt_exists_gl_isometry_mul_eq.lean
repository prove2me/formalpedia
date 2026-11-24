-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mul_eq
-- name    : GlobalTheory.HermWitt.exists_gl_isometry_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:59:11.01604+00:00
-- url     : https://prove2.me/theorems/5425e3ee-d579-4a46-b849-79aaeae8a01a
-- title:
--   Herm Witt: exists gl isometry mul eq
-- statement:
--   The Herm Witt construction uses the exists gl isometry mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L368-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L368-L380

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

theorem GlobalTheory.HermWitt.exists_gl_isometry_mul_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0)
    {m : Type*} [Fintype m] {X Y : Matrix n m E} (h0 : ∀ a, X *ᵥ a = 0 ↔ Y *ᵥ a = 0)
    (hXY : Yᵀ * G * Y.map c = Xᵀ * G * X.map c) :
    ∃ γ : GL n E, (γ : Matrix n n E)ᵀ * G * (γ : Matrix n n E).map c = G ∧
      (γ : Matrix n n E) * X = Y := by sorry
