-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_F_smul
-- name    : GlobalTheory.WittSolve.F_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:32.27619+00:00
-- url     : https://prove2.me/theorems/a9ca6a6c-d3fe-4b51-adc4-4eb752019c42
-- title:
--   Witt Solve: F smul
-- statement:
--   The Witt Solve construction uses the F smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L31-L36

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

theorem GlobalTheory.WittSolve.F_smul (M : Matrix ι ι (WittVector p R)) (n : ℕ) (v : ι → WittVector p R) :
    F M (((p : WittVector p R) ^ n) • v) = ((p : WittVector p R) ^ n) • F M v := by sorry
