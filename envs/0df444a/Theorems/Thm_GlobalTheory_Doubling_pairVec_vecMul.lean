-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_pairVec_vecMul
-- name    : GlobalTheory.Doubling.pairVec_vecMul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:57.64593+00:00
-- url     : https://prove2.me/theorems/53674254-fe9e-40a4-968d-61908799810c
-- title:
--   Doubling: pair Vec vec Mul
-- statement:
--   The Doubling construction uses the pair Vec vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L63-L68

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : m ⊕ n ≃ ι)
variable [Fintype m] [Fintype n] [Fintype ι]

theorem GlobalTheory.Doubling.pairVec_vecMul (M : Matrix ι ι A) (x : m → A) (y : n → A) : pairVec e x y ᵥ* M =
    pairVec e (x ᵥ* (M.submatrix e e).toBlocks₁₁ + y ᵥ* (M.submatrix e e).toBlocks₂₁)
      (x ᵥ* (M.submatrix e e).toBlocks₁₂ + y ᵥ* (M.submatrix e e).toBlocks₂₂) := by sorry
