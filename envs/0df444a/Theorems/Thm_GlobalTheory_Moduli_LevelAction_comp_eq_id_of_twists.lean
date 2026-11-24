-- Prove2me | Theorems.Thm_GlobalTheory_Moduli_LevelAction_comp_eq_id_of_twists
-- name    : GlobalTheory.Moduli.LevelAction.comp_eq_id_of_twists
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:26:57.801441+00:00
-- url     : https://prove2.me/theorems/e0488aa6-0641-489a-9b9a-64ca96741e18
-- title:
--   Level Action: comp eq id of twists
-- statement:
--   The Level Action construction uses the comp eq id of twists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CompEqIdOfTwists.lean#L94-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CompEqIdOfTwists.lean#L94-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.Moduli GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem GlobalTheory.Moduli.LevelAction.comp_eq_id_of_twists {l : Level H} (Xo : Moduli D l) {g g' : Sim D} (hred : IsReduced Xo.X)
    (i : ObjMap Xo.univ Xo.univ (𝟙 _)) {f f' : Xo.X ⟶ Xo.X} (h : Twists Xo g f) (h' : Twists Xo g' f')
    (hM : ∀ a, D.ModN l.M (g.f l.M (g'.f l.M a) - a)) (hA : ∀ a, D.ModN l.A (g.f l.A (g'.f l.A a) - a)) :
    f ≫ f' = 𝟙 _ := by sorry
