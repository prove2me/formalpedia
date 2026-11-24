-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_sepIneq_large
-- name    : GlobalTheory.CuspGL.sepIneq_large
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:32:48.412802+00:00
-- url     : https://prove2.me/theorems/25acba70-857b-4c6d-a728-52ca0746b0c4
-- title:
--   Cusp GL: sep Ineq large
-- statement:
--   The Cusp GL construction uses the sep Ineq large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGL.lean#L34-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGL.lean#L34-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SeparationNumericalIneqCuspidalGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.sepIneq_large (q n : ℕ) (hq : 2 ≤ q) (hn : 11 ≤ n) :
    (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by sorry
