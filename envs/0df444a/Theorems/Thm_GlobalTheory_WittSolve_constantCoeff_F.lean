-- Prove2me | Theorems.Thm_GlobalTheory_WittSolve_constantCoeff_F
-- name    : GlobalTheory.WittSolve.constantCoeff_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:40.847806+00:00
-- url     : https://prove2.me/theorems/0234a31c-8370-4672-b0cf-0e3cf216020a
-- title:
--   Witt Solve: constant Coeff F
-- statement:
--   The Witt Solve construction uses the constant Coeff F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WittVectorExistsUniqueSubMatrixFrobeniusEq.lean#L38-L46

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

theorem GlobalTheory.WittSolve.constantCoeff_F (M : Matrix ι ι (WittVector p R)) (v : ι → WittVector p R) (k : ι) :
    WittVector.constantCoeff (F M v k) =
      ((fun j => WittVector.constantCoeff (v j)) - (M.map WittVector.constantCoeff).mulVec
        (fun j => frobenius R p (WittVector.constantCoeff (v j)))) k := by sorry
