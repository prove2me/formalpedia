-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_C_functionField
-- name    : GroundTheory.Arith.Abelian.algebraMap_C_functionField
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:41:23.958094+00:00
-- url     : https://prove2.me/theorems/2295110e-5945-4e09-89c7-29288eeb5779
-- title:
--   Abelian: algebra Map C function Field
-- statement:
--   The Abelian construction uses the algebra Map C function Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L57-L59

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.algebraMap_C_functionField (c : F) :
    algebraMap F[X] W.toAffine.FunctionField (C c) = algebraMap F W.toAffine.FunctionField c := by sorry
