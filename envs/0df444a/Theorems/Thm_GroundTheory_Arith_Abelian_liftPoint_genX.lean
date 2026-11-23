-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_liftPoint_genX
-- name    : GroundTheory.Arith.Abelian.liftPoint_genX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:46.291052+00:00
-- url     : https://prove2.me/theorems/2c850a29-69f5-46ba-a30f-8aa943af3290
-- title:
--   Abelian: lift Point gen X
-- statement:
--   The Abelian construction uses the lift Point gen X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L110-L113

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

theorem GroundTheory.Arith.Abelian.liftPoint_genX (h : (W.baseChange L).toAffine.Equation u v) (hu : Transcendental F u) :
    liftPoint W h hu (genX W) = u := by sorry
