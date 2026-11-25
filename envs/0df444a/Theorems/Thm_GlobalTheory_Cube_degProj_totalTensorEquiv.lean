-- Prove2me | Theorems.Thm_GlobalTheory_Cube_degProj_totalTensorEquiv
-- name    : GlobalTheory.Cube.degProj_totalTensorEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:42.196033+00:00
-- url     : https://prove2.me/theorems/4c0d2f8c-3f41-5dc6-b21b-27ccd3016798
-- title:
--   Cube: deg Proj total Tensor Equiv
-- statement:
--   The Cube construction uses the deg Proj total Tensor Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L505-L531
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L505-L531

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

theorem GlobalTheory.Cube.degProj_totalTensorEquiv (n : ℕ) (z : (∀ s, A.obj s) ⊗[K] (∀ t, B.obj t)) :
    degProj (extTensor A B) n (totalTensorEquiv A B z) = totalTensorEquiv A B
      ((∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, TensorProduct.map (degProj A x.1) (degProj B x.2) :
        Module.End K _) z) := by sorry
