-- Prove2me | Theorems.Thm_GlobalTheory_EigFlat_piScalarRight_lTensor_vecMul
-- name    : GlobalTheory.EigFlat.piScalarRight_lTensor_vecMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:28.337741+00:00
-- url     : https://prove2.me/theorems/fd0dfcd9-3553-4483-9319-50dc5efd6d91
-- title:
--   Eig Flat: pi Scalar Right l Tensor vec Mul
-- statement:
--   The Eig Flat construction uses the pi Scalar Right l Tensor vec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L11-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]

theorem GlobalTheory.EigFlat.piScalarRight_lTensor_vecMul {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B]
    (x : B ⊗[A] (a → A)) :
    TensorProduct.piScalarRight A B B b (LinearMap.lTensor B U.vecMulLinear x)
      = (TensorProduct.piScalarRight A B B a x) ᵥ* U.map (algebraMap A B) := by sorry
