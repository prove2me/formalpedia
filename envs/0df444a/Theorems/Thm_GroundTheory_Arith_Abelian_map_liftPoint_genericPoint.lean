-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_map_liftPoint_genericPoint
-- name    : GroundTheory.Arith.Abelian.map_liftPoint_genericPoint
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:44.653293+00:00
-- url     : https://prove2.me/theorems/5a92bd95-1944-4f64-9058-282580c258c1
-- title:
--   Abelian: map lift Point generic Point
-- statement:
--   The Abelian construction uses the map lift Point generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L226-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean#L226-L231

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
variable [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.map_liftPoint_genericPoint {L : Type*} [Field L] [Algebra F L] [DecidableEq L] {u v : L}
    (h : (W.baseChange L).toAffine.Nonsingular u v) (hu : Transcendental F u) :
    Point.map (liftPoint W h.1 hu) (genericPoint W) = .some u v h := by sorry
