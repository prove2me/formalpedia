-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_isometry_iff_congr_eq
-- name    : GlobalTheory.HermWitt.isometry_iff_congr_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:50.194119+00:00
-- url     : https://prove2.me/theorems/0e446b0e-d7f5-4f1d-8d09-14b0088f247a
-- title:
--   Herm Witt: isometry iff congr eq
-- statement:
--   The Herm Witt construction uses the isometry iff congr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L281-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L281-L289

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

theorem GlobalTheory.HermWitt.isometry_iff_congr_eq (c : E →+* E) (G P : Matrix n n E) :
    (∀ x y, (P *ᵥ x) ⬝ᵥ G *ᵥ (c ∘ (P *ᵥ y)) = x ⬝ᵥ G *ᵥ (c ∘ y)) ↔ Pᵀ * G * P.map c = G := by sorry
