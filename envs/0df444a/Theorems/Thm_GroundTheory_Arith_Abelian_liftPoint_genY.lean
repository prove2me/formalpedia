-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_liftPoint_genY
-- name    : GroundTheory.Arith.Abelian.liftPoint_genY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:39.606369+00:00
-- url     : https://prove2.me/theorems/342c8056-f0a2-4f59-9e16-3efde9f9210f
-- title:
--   Abelian: lift Point gen Y
-- statement:
--   The Abelian construction uses the lift Point gen Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L115-L118

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
variable {L : Type*} [Field L] [Algebra F L] {u v : L}

theorem GroundTheory.Arith.Abelian.liftPoint_genY (h : (W.baseChange L).toAffine.Equation u v) (hu : Transcendental F u) :
    liftPoint W h hu (genY W) = v := by sorry
