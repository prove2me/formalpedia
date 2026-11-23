-- Prove2me | Theorems.Thm_GlobalTheory_CharpolyPow_card_roots_charpoly
-- name    : GlobalTheory.CharpolyPow.card_roots_charpoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:41.455801+00:00
-- url     : https://prove2.me/theorems/63051b43-86f6-4c18-8da6-a8acfe6a24da
-- title:
--   Charpoly Pow: card roots charpoly
-- statement:
--   The Charpoly Pow construction uses the card roots charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootsCharpolyPowEqMapPow.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootsCharpolyPowEqMapPow.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootsCharpolyPowEqMapPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CharpolyPow
variable {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}

theorem GlobalTheory.CharpolyPow.card_roots_charpoly (M : Matrix (Fin n) (Fin n) k) : Multiset.card M.charpoly.roots = n := by sorry
