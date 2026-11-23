-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_infinite_of_isSepClosed
-- name    : GroundTheory.Arith.Abelian.infinite_of_isSepClosed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:45.990832+00:00
-- url     : https://prove2.me/theorems/3a4957de-6319-46ff-b78e-91ae516454fc
-- title:
--   Abelian: infinite of is Sep Closed
-- statement:
--   The Abelian construction uses the infinite of is Sep Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L46-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/KernelCard.lean#L46-L70

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
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
variable {F : Type*} [Field F] (W : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.infinite_of_isSepClosed (k : Type*) [Field k] [IsSepClosed k] : Infinite k := by sorry
