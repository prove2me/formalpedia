-- Prove2me | Theorems.Thm_GlobalTheory_Cube_res_extTensor
-- name    : GlobalTheory.Cube.res_extTensor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:01.140484+00:00
-- url     : https://prove2.me/theorems/d3d5af8a-13f0-5b7e-8d87-9ca3c4897664
-- title:
--   Cube: res ext Tensor
-- statement:
--   The Cube construction uses the res ext Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L409-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L409-L411

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

theorem GlobalTheory.Cube.res_extTensor (A : Cube.{v} ι K) (B : Cube.{v} κ K) {w w' : Finset (ι ⊕ₗ κ)}
    (h : w ⊆ w') : res (extTensor A B) h =
      TensorProduct.map (res A (monotone_part _ h)) (res B (monotone_part _ h)) := by sorry
