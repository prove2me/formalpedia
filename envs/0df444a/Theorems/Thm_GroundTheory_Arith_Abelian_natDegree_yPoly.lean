-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_yPoly
-- name    : GroundTheory.Arith.Abelian.natDegree_yPoly
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:36:56.963807+00:00
-- url     : https://prove2.me/theorems/cf0d9efb-3769-4b5b-bb16-cc52f8a12528
-- title:
--   Abelian: nat Degree y Poly
-- statement:
--   The Abelian construction uses the nat Degree y Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L15-L16

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

theorem GroundTheory.Arith.Abelian.natDegree_yPoly (x : F) : (yPoly E x).natDegree = 2 := by sorry
