-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_genX_eq
-- name    : GroundTheory.Arith.Abelian.genX_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:19.727444+00:00
-- url     : https://prove2.me/theorems/f7e9b28c-2c1e-4924-9f65-8899bb203ed6
-- title:
--   Abelian: gen X eq
-- statement:
--   The Abelian construction uses the gen X eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L19-L19

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.genX_eq : genX W = algebraMap F[X] W.toAffine.FunctionField X := by sorry
