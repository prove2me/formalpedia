-- Prove2me | Theorems.Thm_GlobalTheory_CubeLawCompare_bijective_app_fst
-- name    : GlobalTheory.CubeLawCompare.bijective_app_fst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:29:02.552471+00:00
-- url     : https://prove2.me/theorems/d718d1c6-e8eb-4294-a672-fcc747114739
-- title:
--   Cube Law Compare: bijective app fst
-- statement:
--   The Cube Law Compare construction uses the bijective app fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocallyTrivialOfIsoPull.lean#L180-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocallyTrivialOfIsoPull.lean#L180-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CubeLawCompare
open scoped CategoryTheory.Obj

theorem GlobalTheory.CubeLawCompare.bijective_app_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A]
    (hA : IsAbelianScheme A) (T : Over S) (V : T.left.Opens) :
    Function.Bijective ((fst T A).left.app V).hom := by sorry
