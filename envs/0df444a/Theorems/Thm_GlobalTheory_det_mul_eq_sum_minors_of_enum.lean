-- Prove2me | Theorems.Thm_GlobalTheory_det_mul_eq_sum_minors_of_enum
-- name    : GlobalTheory.det_mul_eq_sum_minors_of_enum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:44.124127+00:00
-- url     : https://prove2.me/theorems/3da5b677-683a-444d-933e-9c127f191cb9
-- title:
--   Global Theory: det mul eq sum minors of enum
-- statement:
--   The Global Theory construction uses the det mul eq sum minors of enum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L83-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L83-L96

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

theorem GlobalTheory.det_mul_eq_sum_minors_of_enum {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (e : Set.powersetCard n (Fintype.card m) → m → n)
    (he : ∀ S, Set.range (e S) = (S.1 : Set n)) (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ S : Set.powersetCard n (Fintype.card m),
      (A.submatrix id (e S)).det * (B.submatrix (e S) id).det := by sorry
