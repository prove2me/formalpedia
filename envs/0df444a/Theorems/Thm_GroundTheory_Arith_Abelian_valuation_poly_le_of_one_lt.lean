-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_valuation_poly_le_of_one_lt
-- name    : GroundTheory.Arith.Abelian.valuation_poly_le_of_one_lt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:26:57.548914+00:00
-- url     : https://prove2.me/theorems/c5787836-5c0a-4c3d-85d4-d4ad612437d1
-- title:
--   Abelian: valuation poly le of one lt
-- statement:
--   The Abelian construction uses the valuation poly le of one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L115-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsValuation.lean#L115-L123

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

theorem GroundTheory.Arith.Abelian.valuation_poly_le_of_one_lt (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) (p : F[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    w (algebraMap F[X] W.toAffine.FunctionField p) ≤ exp (n * k) := by sorry
