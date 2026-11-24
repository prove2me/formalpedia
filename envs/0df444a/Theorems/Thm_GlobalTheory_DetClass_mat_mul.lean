-- Prove2me | Theorems.Thm_GlobalTheory_DetClass_mat_mul
-- name    : GlobalTheory.DetClass.mat_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:25.764837+00:00
-- url     : https://prove2.me/theorems/4bcdb9b0-f30b-4785-9ffd-fe6ec1bb017e
-- title:
--   Det Class: mat mul
-- statement:
--   The Det Class construction uses the mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdClassGroupMk0EqOfLinearEquivPi.lean#L68-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdClassGroupMk0EqOfLinearEquivPi.lean#L68-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.DetClass
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.DetClass.mat_mul {I J : ι → Ideal R} (φ : ((i : ι) → I i) ≃ₗ[R] ((i : ι) → J i))
    (c : R) (hI : ∀ i, c ∈ I i) (hJ : ∀ i, c ∈ J i) :
    mat φ.symm.toLinearMap (fun i => ⟨c, hJ i⟩) * mat φ.toLinearMap (fun i => ⟨c, hI i⟩)
      = Matrix.diagonal fun _ => c * c := by sorry
