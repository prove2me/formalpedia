-- Prove2me | Theorems.Thm_GlobalTheory_HermWitt_congr_of_fromBlocks_congr_cc
-- name    : GlobalTheory.HermWitt.congr_of_fromBlocks_congr_cc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:30.020058+00:00
-- url     : https://prove2.me/theorems/e435c61c-44a5-4440-b168-c884fc69c6d5
-- title:
--   Herm Witt: congr of from Blocks congr cc
-- statement:
--   The Herm Witt construction uses the congr of from Blocks congr cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L465-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsGlIsometryCompEqOfNondegenerate.lean#L465-L472

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
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.HermWitt.congr_of_fromBlocks_congr_cc {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {D : Matrix m m E} (hD : ∀ a b, FD.cc (D a b) = D b a)
    (hdet : D.det ≠ 0) {G₁ G₂ : Matrix n n E} (hG : ∀ a b, FD.cc (G₁ a b) = G₁ b a)
    {P : Matrix (m ⊕ n) (m ⊕ n) E} (hP : P.det ≠ 0)
    (h : fromBlocks D 0 0 G₂ = Pᵀ * fromBlocks D 0 0 G₁ * P.map FD.cc) :
    ∃ Q : Matrix n n E, Q.det ≠ 0 ∧ G₂ = Qᵀ * G₁ * Q.map FD.cc := by sorry
