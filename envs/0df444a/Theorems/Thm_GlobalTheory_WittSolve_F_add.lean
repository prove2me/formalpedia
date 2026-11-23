-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_F_add
-- name    : GlobalTheory.WittSolve.F_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:35.224881+00:00
-- url     : https://prove2.me/theorems/8ce1f3fb-f41c-45bd-b72e-ec86f6aeb92d
-- title:
--   Witt Solve: F add
-- statement:
--   The Witt Solve construction uses the F add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L14-L19

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

theorem GlobalTheory.WittSolve.F_add (M : Matrix ι ι (WittVector p R)) (v w : ι → WittVector p R) :
    F M (v + w) = F M v + F M w := by sorry
