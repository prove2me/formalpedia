-- Prove2me | Theorems.Thm_GlobalTheory_Cube_cubeSign_inlEmb
-- name    : GlobalTheory.Cube.cubeSign_inlEmb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:46.244869+00:00
-- url     : https://prove2.me/theorems/b48d5bec-f550-48ab-9f2c-67b0db543e04
-- title:
--   Cube: cube Sign inl Emb
-- statement:
--   The Cube construction uses the cube Sign inl Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L424-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L424-L432

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

theorem GlobalTheory.Cube.cubeSign_inlEmb (w : Finset (ι ⊕ₗ κ)) (i : ι) :
    cubeSign w (inlEmb ι κ i) = cubeSign (part (inlEmb ι κ) w) i := by sorry
