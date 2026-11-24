-- Prove2me | Theorems.Thm_GlobalTheory_det_mul_det_eq_of_range_eq
-- name    : GlobalTheory.det_mul_det_eq_of_range_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:53.892657+00:00
-- url     : https://prove2.me/theorems/948fa571-00ad-4eb0-9e7f-d29cfdc6dad2
-- title:
--   Global Theory: det mul det eq of range eq
-- statement:
--   The Global Theory construction uses the det mul det eq of range eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L59-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L59-L81

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

theorem GlobalTheory.det_mul_det_eq_of_range_eq {m k n : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (A : Matrix m n R) (B : Matrix n m R) (φ : k ≃ m) (e : m → n) (g : k → n)
    (hg : Function.Injective g) (h : Set.range e = Set.range g) :
    (A.submatrix id e).det * (B.submatrix e id).det =
      (A.submatrix φ g).det * (B.submatrix g φ).det := by sorry
