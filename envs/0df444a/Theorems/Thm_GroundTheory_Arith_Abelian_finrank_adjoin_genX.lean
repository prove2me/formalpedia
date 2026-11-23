-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_finrank_adjoin_genX
-- name    : GroundTheory.Arith.Abelian.finrank_adjoin_genX
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:31.333012+00:00
-- url     : https://prove2.me/theorems/1fa3d4d1-8929-4065-9c68-d5d5ff4545bc
-- title:
--   Abelian: finrank adjoin gen X
-- statement:
--   The Abelian construction uses the finrank adjoin gen X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L179-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L179-L214

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

theorem GroundTheory.Arith.Abelian.finrank_adjoin_genX : Module.finrank (IntermediateField.adjoin F {genX W})
    W.toAffine.FunctionField = 2 := by sorry
