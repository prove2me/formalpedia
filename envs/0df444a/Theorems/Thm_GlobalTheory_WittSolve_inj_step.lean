-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_inj_step
-- name    : GlobalTheory.WittSolve.inj_step
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:55:52.356922+00:00
-- url     : https://prove2.me/theorems/3f144398-9c30-4b90-bcbc-63ce9ab08d83
-- title:
--   Witt Solve: inj step
-- statement:
--   The Witt Solve construction uses the inj step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L61-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L61-L86

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
variable {M : Matrix ι ι (WittVector p R)}

theorem GlobalTheory.WittSolve.inj_step
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (v : ι → WittVector p R) (hv : F M v = 0) :
    ∃ w : ι → WittVector p R, v = (p : WittVector p R) • w ∧ F M w = 0 := by sorry
