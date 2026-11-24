-- Prove2me | Theorems.Thm_GlobalTheory_matrix_rank_sub_le
-- name    : GlobalTheory.matrix_rank_sub_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:17.303835+00:00
-- url     : https://prove2.me/theorems/856e695e-1bc2-4e0a-9a3d-d1a5f1dd095a
-- title:
--   Global Theory: matrix rank sub le
-- statement:
--   The Global Theory construction uses the matrix rank sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L369-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsIsSymplecticBasisToMatrixOffDiagDvd.lean#L369-L375

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {R : Type*} [CommRing R] {l n : Type*} [Fintype l] [DecidableEq l] [Fintype n]
  [DecidableEq n]
omit [DecidableEq n]

theorem GlobalTheory.matrix_rank_sub_le {K : Type*} [Field K] (A B : Matrix n n K) :
    (A - B).rank ≤ A.rank + B.rank := by sorry
