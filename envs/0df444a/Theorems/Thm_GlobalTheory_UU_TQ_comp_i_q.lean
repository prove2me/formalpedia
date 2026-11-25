-- Prove2me | Theorems.Thm_GlobalTheory_UU_TQ_comp_i_q
-- name    : GlobalTheory.UU.TQ.comp_i_q
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:01:31.936262+00:00
-- url     : https://prove2.me/theorems/1104fb9a-42ac-5452-8b1f-bff734c7767c
-- title:
--   TQ: comp i q
-- statement:
--   The TQ construction uses the comp i q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L15-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]

theorem GlobalTheory.UU.TQ.comp_i_q (Q : TQ G X) {T : Over S} (t : T ⟶ splitTorus S X) : (t ≫ Q.i) ≫ Q.q = 1 := by sorry
