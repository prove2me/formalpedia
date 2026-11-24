-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_apply_lid_rTensor
-- name    : GlobalTheory.KuennethOne.apply_lid_rTensor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:48.7868+00:00
-- url     : https://prove2.me/theorems/9f97121f-fa56-40b2-908f-793093452e87
-- title:
--   Kuenneth One: apply lid r Tensor
-- statement:
--   The Kuenneth One construction uses the apply lid r Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineOpenInfOfIsSeparated.lean#L24-L30

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

theorem GlobalTheory.KuennethOne.apply_lid_rTensor {R C B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] R) (w : C ⊗[R] B) :
    f (TensorProduct.lid R B (l.rTensor B w)) = l (TensorProduct.rid R C (f.lTensor C w)) := by sorry
