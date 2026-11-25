-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_tensor_left_of_smooth_grpObj
-- name    : GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:41:49.62037+00:00
-- url     : https://prove2.me/theorems/cdad81d0-e47f-4822-9108-dff7c43ffdb7
-- title:
--   Global Theory: is Integral tensor left of smooth grp Obj
-- statement:
--   The Global Theory construction uses the is Integral tensor left of smooth grp Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIntegralTensorLeftOfSmoothGrpObj.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIntegralTensorLeftOfSmoothGrpObj.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.isIntegral_tensor_left_of_smooth_grpObj (S : Scheme.{0}) (B T : Over S) [GrpObj B]
    [Smooth B.hom] [GeometricallyConnected B.hom] [IsIntegral T.left] :
    IsIntegral (T ⊗ B).left := by sorry
