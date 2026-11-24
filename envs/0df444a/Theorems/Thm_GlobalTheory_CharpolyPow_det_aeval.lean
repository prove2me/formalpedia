-- Prove2me | Theorems.Thm_GlobalTheory_CharpolyPow_det_aeval
-- name    : GlobalTheory.CharpolyPow.det_aeval
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:10:09.591091+00:00
-- url     : https://prove2.me/theorems/f8568b12-bf21-4075-9a95-c25505c5b51b
-- title:
--   Charpoly Pow: det aeval
-- statement:
--   The Charpoly Pow construction uses the det aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootsCharpolyPowEqMapPow.lean#L40-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootsCharpolyPowEqMapPow.lean#L40-L62

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

theorem GlobalTheory.CharpolyPow.det_aeval (M : Matrix (Fin n) (Fin n) k) (q : k[X]) :
    (aeval M q).det = (M.charpoly.roots.map (fun z => eval z q)).prod := by sorry
