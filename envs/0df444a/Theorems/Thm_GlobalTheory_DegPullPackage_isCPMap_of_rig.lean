-- Prove2me | Theorems.Thm_GlobalTheory_DegPullPackage_isCPMap_of_rig
-- name    : GlobalTheory.DegPullPackage.isCPMap_of_rig
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:55:27.207729+00:00
-- url     : https://prove2.me/theorems/a2f62f57-0dcc-4b1e-99ee-387595af28df
-- title:
--   Deg Pull Package: is CPMap of rig
-- statement:
--   The Deg Pull Package construction uses the is CPMap of rig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsCubicalBundleMapOfPulledBackDegeneration.lean#L21-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsCubicalBundleMapOfPulledBackDegeneration.lean#L21-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsCubicalBundleMapOfPulledBackDegeneration
import Theorems.Thm_GlobalTheory_UU_IsWt_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory GlobalTheory.DegPullPackage

theorem GlobalTheory.DegPullPackage.isCPMap_of_rig (hG : GlobalFnsSt) {S S' : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]
    {f : S' ⟶ S} {B' : Over S'} [GrpObj B'] [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B')
    {β : B'.left ⟶ B.left} {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen)
    (he : eSec B' ≫ β = f ≫ eSec B)
    (hr' : PMaps w (fun _ : PUnit => eSec B') (fun _ => eSec B) (fun _ => 1) M'.L.rig M.L.rig f) :
    IsCPMap M' M f β hw w := by sorry
