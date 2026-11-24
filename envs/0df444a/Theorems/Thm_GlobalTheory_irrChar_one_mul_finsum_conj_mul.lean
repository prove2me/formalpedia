-- Prove2me | Theorems.Thm_GlobalTheory_irrChar_one_mul_finsum_conj_mul
-- name    : GlobalTheory.irrChar_one_mul_finsum_conj_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:13.881177+00:00
-- url     : https://prove2.me/theorems/0eec5b68-a0a0-4a7b-91ea-bd304aaac920
-- title:
--   Global Theory: irr Char one mul finsum conj mul
-- statement:
--   The Global Theory construction uses the irr Char one mul finsum conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrrCharOneMulFinsumConjMul.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrrCharOneMulFinsumConjMul.lean#L43-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrrCharOneMulFinsumConjMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory

theorem GlobalTheory.irrChar_one_mul_finsum_conj_mul : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsIrrChar ℂ ℂ χ → ∀ x y : G, χ 1 * ∑ᶠ h : G, χ (h * x * h⁻¹ * y) = (Nat.card G : ℂ) * (χ x * χ y) := by sorry
