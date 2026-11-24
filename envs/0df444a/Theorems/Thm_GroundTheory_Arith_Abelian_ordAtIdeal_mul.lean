-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ordAtIdeal_mul
-- name    : GroundTheory.Arith.Abelian.ordAtIdeal_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:08.550736+00:00
-- url     : https://prove2.me/theorems/5a86526c-99e9-4da5-a312-546719a6f8c0
-- title:
--   Abelian: ord At Ideal mul
-- statement:
--   The Abelian construction uses the ord At Ideal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L187-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsOrd.lean#L187-L192

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

theorem GroundTheory.Arith.Abelian.ordAtIdeal_mul (v : HeightOneSpectrum W.toAffine.CoordinateRing)
    {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordAtIdeal W v (f * g) = ordAtIdeal W v f + ordAtIdeal W v g := by sorry
