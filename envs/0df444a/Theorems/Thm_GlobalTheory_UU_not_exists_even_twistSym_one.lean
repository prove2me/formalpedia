-- Prove2me | Theorems.Thm_GlobalTheory_UU_not_exists_even_twistSym_one
-- name    : GlobalTheory.UU.not_exists_even_twistSym_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:08.461515+00:00
-- url     : https://prove2.me/theorems/bf93eb42-e1ac-4ffb-955a-7768abbab0a1
-- title:
--   UU: not exists even twist Sym one
-- statement:
--   The UU construction uses the not exists even twist Sym one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L144-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/NotExistsEvenTwistSymOne.lean#L144-L169

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

theorem GlobalTheory.UU.not_exists_even_twistSym_one :
    ¬ ∃ σ : CubTriv ((CP.triv (splitTorus (Spec (CommRingCat.of ℚ)) ℤ)).twistSym 1).c (𝟙 _), σ.Even := by sorry
