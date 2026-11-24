-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_smul_basis
-- name    : GroundTheory.Arith.Abelian.algebraMap_smul_basis
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:41:15.137519+00:00
-- url     : https://prove2.me/theorems/b8cd57d5-9f9c-409e-ba8b-a7615812aafa
-- title:
--   Abelian: algebra Map smul basis
-- statement:
--   The Abelian construction uses the algebra Map smul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L70-L77

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

theorem GroundTheory.Arith.Abelian.algebraMap_smul_basis (p q : F[X]) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X) =
      algebraMap F[X] W.toAffine.FunctionField p +
        algebraMap F[X] W.toAffine.FunctionField q * genY W := by sorry
