-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_mul
-- name    : GroundTheory.Arith.Abelian.ordInfty_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:41:16.335659+00:00
-- url     : https://prove2.me/theorems/cece8739-2d31-4c0e-a4a2-326e232fdedc
-- title:
--   Abelian: ord Infty mul
-- statement:
--   The Abelian construction uses the ord Infty mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L106-L109

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
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

theorem GroundTheory.Arith.Abelian.ordInfty_mul {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f * g) = ordInfty W f + ordInfty W g := by sorry
