-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_inv
-- name    : GroundTheory.Arith.Abelian.ordInfty_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:27:08.725799+00:00
-- url     : https://prove2.me/theorems/9032b9a0-e84c-4f76-961b-fcdcf99c9bfe
-- title:
--   Abelian: ord Infty inv
-- statement:
--   The Abelian construction uses the ord Infty inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L111-L112

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

theorem GroundTheory.Arith.Abelian.ordInfty_inv (f : W.toAffine.FunctionField) : ordInfty W f⁻¹ = -ordInfty W f := by sorry
