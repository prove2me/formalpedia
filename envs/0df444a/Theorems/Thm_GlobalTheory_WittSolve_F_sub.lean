-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_F_sub
-- name    : GlobalTheory.WittSolve.F_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:56:05.228487+00:00
-- url     : https://prove2.me/theorems/25fb60b5-55e1-49f8-841b-a743e1a10711
-- title:
--   Witt Solve: F sub
-- statement:
--   The Witt Solve construction uses the F sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L25-L29

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

theorem GlobalTheory.WittSolve.F_sub (M : Matrix ι ι (WittVector p R)) (v w : ι → WittVector p R) :
    F M (v - w) = F M v - F M w := by sorry
