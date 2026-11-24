-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordPoint_mul
-- name    : GroundTheory.Arith.Abelian.ordPoint_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:56.979195+00:00
-- url     : https://prove2.me/theorems/4d5b1fd3-582a-4676-a774-ff69928fe52d
-- title:
--   Abelian: ord Point mul
-- statement:
--   The Abelian construction uses the ord Point mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L244-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L244-L248

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
variable [IsAlgClosed F] [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.ordPoint_mul (P : W.toAffine.Point) {f g : W.toAffine.FunctionField} (hf : f ≠ 0)
    (hg : g ≠ 0) : ordPoint W P (f * g) = ordPoint W P f + ordPoint W P g := by sorry
