-- Prove2me | Theorems.Thm_GlobalTheory_UU_TorusCompat_of_comp_right
-- name    : GlobalTheory.UU.TorusCompat.of_comp_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:43:17.676208+00:00
-- url     : https://prove2.me/theorems/cf64add9-9b06-5ad9-b790-0ea570b02f87
-- title:
--   Torus Compat: of comp right
-- statement:
--   The Torus Compat construction uses the of comp right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueTorusCompat.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueTorusCompat.lean#L122-L132

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
open SplitTorus (bcMap bcMap_hom)
variable {S S' S'' : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G'' : Over S''} {G' : Over S'} {G : Over S}

theorem GlobalTheory.UU.TorusCompat.of_comp_right {f' : S'' ⟶ S'} {f : S' ⟶ S} {F' : G''.left ⟶ G'.left}
    {F : G'.left ⟶ G.left} (hF : IsPullback F G'.hom G.hom f) (hF' : F' ≫ G'.hom = G''.hom ≫ f')
    {i'' : splitTorus S'' X ⟶ G''} {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G}
    (h'' : TorusCompat (f' ≫ f) (F' ≫ F) i'' i) (h : TorusCompat f F i' i) :
    TorusCompat f' F' i'' i' := by sorry
