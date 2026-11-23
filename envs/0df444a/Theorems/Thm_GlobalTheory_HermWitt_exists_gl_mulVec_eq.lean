-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_exists_gl_mulVec_eq
-- name    : GlobalTheory.HermWitt.exists_gl_mulVec_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:29.86007+00:00
-- url     : https://prove2.me/theorems/6a48582e-a036-40ae-b8b4-7bf7e43bb25b
-- title:
--   Herm Witt: exists gl mul Vec eq
-- statement:
--   The Herm Witt construction uses the exists gl mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L300-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L300-L304

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

theorem GlobalTheory.HermWitt.exists_gl_mulVec_eq (γ : (n → E) ≃ₗ[E] (n → E)) :
    ∃ g : GL n E, ∀ x, (g : Matrix n n E) *ᵥ x = γ x := by sorry
