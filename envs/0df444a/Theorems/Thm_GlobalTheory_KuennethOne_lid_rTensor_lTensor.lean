-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_lid_rTensor_lTensor
-- name    : GlobalTheory.KuennethOne.lid_rTensor_lTensor
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:49.612615+00:00
-- url     : https://prove2.me/theorems/828b4717-3cd2-43a3-870e-12e14b1b8c3b
-- title:
--   Kuenneth One: lid r Tensor l Tensor
-- statement:
--   The Kuenneth One construction uses the lid r Tensor l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L15-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KuennethOne
open TopologicalSpace TensorProduct

theorem GlobalTheory.KuennethOne.lid_rTensor_lTensor {R C A B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] A)
    (w : C ⊗[R] B) : TensorProduct.lid R A (l.rTensor A (f.lTensor C w)) =
      f (TensorProduct.lid R B (l.rTensor B w)) := by sorry
