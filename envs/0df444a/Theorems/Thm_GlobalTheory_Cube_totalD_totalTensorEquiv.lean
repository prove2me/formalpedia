-- Prove2me | Theorems.Thm_GlobalTheory_Cube_totalD_totalTensorEquiv
-- name    : GlobalTheory.Cube.totalD_totalTensorEquiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:37:27.212666+00:00
-- url     : https://prove2.me/theorems/8a9611e3-8c8b-46f8-b8fb-7847c5c16a26
-- title:
--   Cube: total D total Tensor Equiv
-- statement:
--   The Cube construction uses the total D total Tensor Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L467-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L467-L503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]
variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)

theorem GlobalTheory.Cube.totalD_totalTensorEquiv (z : (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t)) :
    totalD (extTensor A B) (totalTensorEquiv A B z) = totalTensorEquiv A B
      ((TensorProduct.map (totalD A) 1 + TensorProduct.map (degSign A) (totalD B) :
        Module.End K _) z) := by sorry
