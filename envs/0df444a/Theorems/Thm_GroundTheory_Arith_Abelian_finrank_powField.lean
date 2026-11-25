-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_finrank_powField
-- name    : GroundTheory.Arith.Abelian.finrank_powField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:37.597805+00:00
-- url     : https://prove2.me/theorems/597ef7ae-5e70-4972-82f4-5a71dd7b60f9
-- title:
--   Abelian: finrank pow Field
-- statement:
--   The Abelian construction uses the finrank pow Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L262-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L262-L270

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
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]

theorem GroundTheory.Arith.Abelian.finrank_powField : Module.finrank (powField E p) E.toAffine.FunctionField = p := by sorry
