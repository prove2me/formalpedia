-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_norm_smul_basis_of_ne_zero
-- name    : GroundTheory.Arith.Abelian.natDegree_norm_smul_basis_of_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:49.072045+00:00
-- url     : https://prove2.me/theorems/622859a1-d66b-4fec-8611-7c7e4b24b2be
-- title:
--   Abelian: nat Degree norm smul basis of ne zero
-- statement:
--   The Abelian construction uses the nat Degree norm smul basis of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L225-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L225-L233

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

theorem GroundTheory.Arith.Abelian.natDegree_norm_smul_basis_of_ne_zero {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) +
      q • AdjoinRoot.mk W.toAffine.polynomial X)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by sorry
