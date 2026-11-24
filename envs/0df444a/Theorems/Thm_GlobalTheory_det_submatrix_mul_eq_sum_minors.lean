-- Prove2me | Theorems.Thm_GlobalTheory_det_submatrix_mul_eq_sum_minors
-- name    : GlobalTheory.det_submatrix_mul_eq_sum_minors
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:46.702411+00:00
-- url     : https://prove2.me/theorems/45f5af53-57bd-49ba-b7d4-ee89da6b9f50
-- title:
--   Global Theory: det submatrix mul eq sum minors
-- statement:
--   The Global Theory construction uses the det submatrix mul eq sum minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L98-L103

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

theorem GlobalTheory.det_submatrix_mul_eq_sum_minors {l n o : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix l n R) (B : Matrix n o R) (r : Fin i → l) (c : Fin i → o) :
    ((A * B).submatrix r c).det = ∑ S : Set.powersetCard n i,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by sorry
