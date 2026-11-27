-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_isSeparable_genY
-- name    : GroundTheory.Arith.Abelian.isSeparable_genY
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:07.616671+00:00
-- url     : https://prove2.me/theorems/7845cba1-8105-59bc-a239-dba3a4cad67c
-- title:
--   Abelian: is Separable gen Y
-- statement:
--   The Abelian construction uses the is Separable gen Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L289-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L289-L313

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
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
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem GroundTheory.Arith.Abelian.isSeparable_genY (L : IntermediateField F E.toAffine.FunctionField)
    (hL : L ≤ F⟮genX E⟯) : IsSeparable (extendScalars hL) (genY E) := by sorry
