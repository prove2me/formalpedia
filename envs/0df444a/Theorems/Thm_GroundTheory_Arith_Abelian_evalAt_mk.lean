-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_evalAt_mk
-- name    : GroundTheory.Arith.Abelian.evalAt_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:38.043445+00:00
-- url     : https://prove2.me/theorems/c84603f9-7243-4b1d-b06b-f7a6dfca2acb
-- title:
--   Abelian: eval At mk
-- statement:
--   The Abelian construction uses the eval At mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L69-L73

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

theorem GroundTheory.Arith.Abelian.evalAt_mk (h : (W.baseChange L).toAffine.Equation u v) (p : F[X][Y]) :
    evalAt W h (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom (algebraMap F L) u) v := by sorry
