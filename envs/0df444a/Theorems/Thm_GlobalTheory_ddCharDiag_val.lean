-- Prove2me | Theorems.Thm_GlobalTheory_ddCharDiag_val
-- name    : GlobalTheory.ddCharDiag_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:09.019112+00:00
-- url     : https://prove2.me/theorems/74e46b1b-16f4-4b02-8777-0c6c319be6d6
-- title:
--   Global Theory: dd Char Diag val
-- statement:
--   The Global Theory construction uses the dd Char Diag val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeneralLinearGroupCharEqOneOfDetEqOne.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/GeneralLinearGroupCharEqOneOfDetEqOne.lean#L129-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]

theorem GlobalTheory.ddCharDiag_val (d : n → Rˣ) :
    ((ddCharDiag d : GL n R) : Matrix n n R) = diagonal fun i => (d i : R) := by sorry
