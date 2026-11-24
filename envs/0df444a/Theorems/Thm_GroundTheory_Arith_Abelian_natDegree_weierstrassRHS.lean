-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_weierstrassRHS
-- name    : GroundTheory.Arith.Abelian.natDegree_weierstrassRHS
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:41:51.748961+00:00
-- url     : https://prove2.me/theorems/e4b18cd7-5896-4f31-99fd-030d21a0351c
-- title:
--   Abelian: nat Degree weierstrass RHS
-- statement:
--   The Abelian construction uses the nat Degree weierstrass RHS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L140-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L140-L141

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
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

theorem GroundTheory.Arith.Abelian.natDegree_weierstrassRHS : (weierstrassRHS W).natDegree = 3 := by sorry
