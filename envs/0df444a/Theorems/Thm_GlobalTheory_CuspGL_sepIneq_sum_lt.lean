-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_sepIneq_sum_lt
-- name    : GlobalTheory.CuspGL.sepIneq_sum_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:32:33.346367+00:00
-- url     : https://prove2.me/theorems/58b2d856-6f52-4e7e-931d-0a4495815a04
-- title:
--   Cusp GL: sep Ineq sum lt
-- statement:
--   The Cusp GL construction uses the sep Ineq sum lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGL.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SeparationNumericalIneqCuspidalGL.lean#L13-L32

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

theorem GlobalTheory.CuspGL.sepIneq_sum_lt (q n : ℕ) (hq : 2 ≤ q) :
    ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < q ^ (n / 2 + 1) := by sorry
