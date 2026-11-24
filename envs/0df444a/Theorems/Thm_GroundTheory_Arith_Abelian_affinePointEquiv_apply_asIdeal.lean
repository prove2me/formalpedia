-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_affinePointEquiv_apply_asIdeal
-- name    : GroundTheory.Arith.Abelian.affinePointEquiv_apply_asIdeal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:32.561598+00:00
-- url     : https://prove2.me/theorems/c4cb1ee9-a96f-4ee8-9ca7-b42bf4f4404d
-- title:
--   Abelian: affine Point Equiv apply as Ideal
-- statement:
--   The Abelian construction uses the affine Point Equiv apply as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Divisors.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Divisors.lean#L181-L182

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
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
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable [IsAlgClosed F]
variable [W.IsElliptic]

theorem GroundTheory.Arith.Abelian.affinePointEquiv_apply_asIdeal (p : {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2}) :
    (affinePointEquiv W p).asIdeal = XYIdeal W.toAffine p.1.1 (C p.1.2) := by sorry
