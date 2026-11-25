-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_yPoly_ne_zero
-- name    : GroundTheory.Arith.Abelian.yPoly_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:40:33.876938+00:00
-- url     : https://prove2.me/theorems/f8068aab-e39e-40ea-8511-440cf689979f
-- title:
--   Abelian: y Poly ne zero
-- statement:
--   The Abelian construction uses the y Poly ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.yPoly_ne_zero (x : F) : yPoly E x ≠ 0 := by sorry
