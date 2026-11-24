-- Prove2me | Theorems.Thm_GlobalTheory_character_one_mul_sum_conj_mul
-- name    : GlobalTheory.character_one_mul_sum_conj_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:49.36696+00:00
-- url     : https://prove2.me/theorems/37ba506e-3edf-49f7-9bb8-127c339552ba
-- title:
--   Global Theory: character one mul sum conj mul
-- statement:
--   The Global Theory construction uses the character one mul sum conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrrCharOneMulFinsumConjMul.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IrrCharOneMulFinsumConjMul.lean#L29-L41

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

theorem GlobalTheory.character_one_mul_sum_conj_mul {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x y : G) :
    ρ.character 1 * ∑ h : G, ρ.character (h * x * h⁻¹ * y)
      = (Fintype.card G : ℂ) * (ρ.character x * ρ.character y) := by sorry
