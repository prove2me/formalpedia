-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_dotProduct_congr_mulVec
-- name    : GlobalTheory.HermWitt.dotProduct_congr_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:28.333681+00:00
-- url     : https://prove2.me/theorems/bcfddf14-f478-49d9-b4ac-188f8e26574e
-- title:
--   Herm Witt: dot Product congr mul Vec
-- statement:
--   The Herm Witt construction uses the dot Product congr mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L274-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L274-L279

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
omit [DecidableEq n]

theorem GlobalTheory.HermWitt.dotProduct_congr_mulVec {m : Type*} [Fintype m] (c : E →+* E) (G : Matrix n n E)
    (P : Matrix n m E) (x y : m → E) :
    x ⬝ᵥ (Pᵀ * G * P.map c) *ᵥ (c ∘ y) = (P *ᵥ x) ⬝ᵥ G *ᵥ (c ∘ (P *ᵥ y)) := by sorry
