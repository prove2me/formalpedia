-- Prove2me | Theorems.Thm_GlobalTheory_T_isPrimitive_extendZero_of_sum_unipotentRadical
-- name    : GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:49:03.295718+00:00
-- url     : https://prove2.me/theorems/5410b63d-8b7e-491c-b248-ab885ab63816
-- title:
--   T: is Primitive extend Zero of sum unipotent Radical
-- statement:
--   The T construction uses the is Primitive extend Zero of sum unipotent Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsPrimitiveExtendZeroOfSumUnipotentRadicalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isPrimitive_extendZero_of_sum_unipotentRadical : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), IsChar ℂ ℂ χ → (∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, χ u = 0) → IsPrimitive (extZero χ) := by sorry
