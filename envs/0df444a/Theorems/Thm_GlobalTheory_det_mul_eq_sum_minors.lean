-- Prove2me | Theorems.Thm_GlobalTheory_det_mul_eq_sum_minors
-- name    : GlobalTheory.det_mul_eq_sum_minors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:40.825309+00:00
-- url     : https://prove2.me/theorems/1ac02ae3-bed0-49e5-b3b6-98c6cbd19481
-- title:
--   Global Theory: det mul eq sum minors
-- statement:
--   The Global Theory construction uses the det mul eq sum minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L40-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {R : Type*} [CommRing R]

theorem GlobalTheory.det_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (B : Matrix n (Fin i) R) :
    (A * B).det = ∑ S : Set.powersetCard n i,
      (A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det := by sorry
