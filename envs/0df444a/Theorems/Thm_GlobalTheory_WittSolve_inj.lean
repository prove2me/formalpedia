-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_inj
-- name    : GlobalTheory.WittSolve.inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:02.798194+00:00
-- url     : https://prove2.me/theorems/fd665a75-10a5-44f0-aa4a-91838ffa70dd
-- title:
--   Witt Solve: inj
-- statement:
--   The Witt Solve construction uses the inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L88-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L88-L104

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

theorem GlobalTheory.WittSolve.inj
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (v : ι → WittVector p R) (hv : F M v = 0) : v = 0 := by sorry
