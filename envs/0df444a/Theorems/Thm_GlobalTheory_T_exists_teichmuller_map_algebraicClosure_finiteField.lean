-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_teichmuller_map_algebraicClosure_finiteField
-- name    : GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:38:09.91906+00:00
-- url     : https://prove2.me/theorems/2e806ef6-db09-4dda-acc8-7a6cfbe375c6
-- title:
--   T: exists teichmuller map algebraic Closure finite Field
-- statement:
--   The T construction uses the exists teichmuller map algebraic Closure finite Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement
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

theorem GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField : ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ, ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by sorry
