-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_valuation_eq_exp_neg_ordAtIdeal
-- name    : GroundTheory.Arith.Abelian.valuation_eq_exp_neg_ordAtIdeal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:03.7619+00:00
-- url     : https://prove2.me/theorems/6c4be9e2-961d-4617-8de3-9e594b9a28e7
-- title:
--   Abelian: valuation eq exp neg ord At Ideal
-- statement:
--   The Abelian construction uses the valuation eq exp neg ord At Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L202-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L202-L223

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

theorem GroundTheory.Arith.Abelian.valuation_eq_exp_neg_ordAtIdeal (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    v.valuation W.toAffine.FunctionField f = exp (-ordAtIdeal W v f) := by sorry
