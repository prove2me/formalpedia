-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_ratEmb_X
-- name    : GroundTheory.Arith.Abelian.ratEmb_X
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:27.904005+00:00
-- url     : https://prove2.me/theorems/7525411f-778f-44a8-83ff-21547fba32fa
-- title:
--   Abelian: rat Emb X
-- statement:
--   The Abelian construction uses the rat Emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L106-L109

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
omit [E.IsElliptic]

theorem GroundTheory.Arith.Abelian.ratEmb_X : ratEmb E RatFunc.X = genX E := by sorry
