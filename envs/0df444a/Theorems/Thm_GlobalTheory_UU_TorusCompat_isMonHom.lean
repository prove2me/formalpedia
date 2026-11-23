-- Prove2me | Theorems.Thm_GlobalTheory_UU_TorusCompat_isMonHom
-- name    : GlobalTheory.UU.TorusCompat.isMonHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:20.107671+00:00
-- url     : https://prove2.me/theorems/bf98c82b-8678-42e4-af76-2e37c4953d18
-- title:
--   Torus Compat: is Mon Hom
-- statement:
--   The Torus Compat construction uses the is Mon Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueTorusCompat.lean#L158-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueTorusCompat.lean#L158-L173

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

theorem GlobalTheory.UU.TorusCompat.isMonHom [GrpObj G'] [GrpObj G] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (hF : IsGrpPullback G' G f F) {i' : splitTorus S' X ⟶ G'} {i : splitTorus S X ⟶ G} [IsMonHom i]
    (h : TorusCompat f F i' i) : IsMonHom i' := by sorry
