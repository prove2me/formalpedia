-- Prove2me | Theorems.Thm_GlobalTheory_SecPullIso_gs_sec_trans
-- name    : GlobalTheory.SecPullIso.gs_sec_trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:58:21.100501+00:00
-- url     : https://prove2.me/theorems/86a788cf-99b1-420e-8042-f546f3cf1a4d
-- title:
--   Sec Pull Iso: gs sec trans
-- statement:
--   The Sec Pull Iso construction uses the gs sec trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionPull.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionPull.lean#L16-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecPullIso

theorem GlobalTheory.SecPullIso.gs_sec_trans {X Z : Scheme.{0}} {L : LB X} (s : LB.Sec L) (r : Z ⟶ X) (z : Z) {j j' : L.ι}
    (hj : r z ∈ L.U j) (hj' : r z ∈ L.U j') :
    gs r z (L.U j) (s.f j) = (gm r z (L.U j ⊓ L.U j') (L.g j j')).val * gs r z (L.U j') (s.f j') := by sorry
