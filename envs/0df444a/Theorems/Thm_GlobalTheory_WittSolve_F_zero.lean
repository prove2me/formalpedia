-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_F_zero
-- name    : GlobalTheory.WittSolve.F_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:09.830512+00:00
-- url     : https://prove2.me/theorems/5602d826-25c2-4bdf-a494-2cf885e36acc
-- title:
--   Witt Solve: F zero
-- statement:
--   The Witt Solve construction uses the F zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L21-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittSolve
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]

theorem GlobalTheory.WittSolve.F_zero (M : Matrix ι ι (WittVector p R)) : F M 0 = 0 := by sorry
