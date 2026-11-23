-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_congr_of_fromBlocks_congr
-- name    : GlobalTheory.HermWitt.congr_of_fromBlocks_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:22.692146+00:00
-- url     : https://prove2.me/theorems/692e6727-9b84-4de7-8939-34ef4f340b60
-- title:
--   Herm Witt: congr of from Blocks congr
-- statement:
--   The Herm Witt construction uses the congr of from Blocks congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L398-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L398-L443

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

theorem GlobalTheory.HermWitt.congr_of_fromBlocks_congr (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {m : Type*} [Fintype m] [DecidableEq m] {D : Matrix m m E} (hD : ∀ a b, c (D a b) = D b a)
    (hdet : D.det ≠ 0) {G₁ G₂ : Matrix n n E} (hG : ∀ a b, c (G₁ a b) = G₁ b a)
    {P : Matrix (m ⊕ n) (m ⊕ n) E} (hP : P.det ≠ 0)
    (h : fromBlocks D 0 0 G₂ = Pᵀ * fromBlocks D 0 0 G₁ * P.map c) :
    ∃ Q : Matrix n n E, Q.det ≠ 0 ∧ G₂ = Qᵀ * G₁ * Q.map c := by sorry
