-- Prove2me | Theorems.Thm_GlobalTheory_Cube_totalTensorEquiv_tmul
-- name    : GlobalTheory.Cube.totalTensorEquiv_tmul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:20.732392+00:00
-- url     : https://prove2.me/theorems/918b9f89-dac9-456a-8e21-74db4f4d412d
-- title:
--   Cube: total Tensor Equiv tmul
-- statement:
--   The Cube construction uses the total Tensor Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L464-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L464-L465

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

theorem GlobalTheory.Cube.totalTensorEquiv_tmul (x : ∀ s, A.obj s) (y : ∀ t, B.obj t) (w : Finset (ι ⊕ₗ κ)) :
    totalTensorEquiv A B (x ⊗ₜ y) w = x (part (inlEmb ι κ) w) ⊗ₜ[K] y (part (inrEmb ι κ) w) := by sorry
