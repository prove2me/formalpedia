-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_unipotent_radical_eq_zero_of_isPrimitive
-- name    : GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:02.823176+00:00
-- url     : https://prove2.me/theorems/dfed6a10-be2c-4411-8b0b-630256c85c49
-- title:
--   T: finsum unipotent radical eq zero of is Primitive
-- statement:
--   The T construction uses the finsum unipotent radical eq zero of is Primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumUnipotentRadicalEqZeroStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumUnipotentRadicalEqZeroStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumUnipotentRadicalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumUnipotentRadicalEqZeroStatement
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

theorem GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (φ : Module.End F (Fin d → F) → ℂ), IsPrimitive φ → ∀ a : ℕ, 0 < a → a < d → ∑ᶠ u ∈ {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}, φ (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)) = 0 := by sorry
