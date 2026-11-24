-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_norm_smul_basis_of_q_eq_zero
-- name    : GroundTheory.Arith.Abelian.natDegree_norm_smul_basis_of_q_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:49.29873+00:00
-- url     : https://prove2.me/theorems/e32a518a-0f09-4d62-bd3c-6119c5f9d2a6
-- title:
--   Abelian: nat Degree norm smul basis of q eq zero
-- statement:
--   The Abelian construction uses the nat Degree norm smul basis of q eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L210-L214

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
variable {W}

theorem GroundTheory.Arith.Abelian.natDegree_norm_smul_basis_of_q_eq_zero {p : F[X]} :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) + (0 : F[X]) •
      AdjoinRoot.mk W.toAffine.polynomial X)).natDegree = 2 * p.natDegree := by sorry
