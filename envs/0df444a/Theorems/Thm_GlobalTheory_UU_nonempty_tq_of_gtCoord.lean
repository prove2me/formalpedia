-- Prove2me | Theorems.Thm_GlobalTheory_UU_nonempty_tq_of_gtCoord
-- name    : GlobalTheory.UU.nonempty_tq_of_gtCoord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:21:27.503923+00:00
-- url     : https://prove2.me/theorems/bbf1ba03-0c6d-52b8-b368-cc01809f8feb
-- title:
--   UU: nonempty tq of gt Coord
-- statement:
--   The UU construction uses the nonempty tq of gt Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L375-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L375-L377

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

theorem GlobalTheory.UU.nonempty_tq_of_gtCoord {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : ∃ Q : TQ (thickObj R I e G) D.X, Q.i = g.i := by sorry
