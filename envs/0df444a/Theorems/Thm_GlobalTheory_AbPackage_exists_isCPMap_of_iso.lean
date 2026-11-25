-- Prove2me | Theorems.Thm_GlobalTheory_AbPackage_exists_isCPMap_of_iso
-- name    : GlobalTheory.AbPackage.exists_isCPMap_of_iso
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:40:34.21693+00:00
-- url     : https://prove2.me/theorems/f5c97f78-32b2-4a08-9e36-1cc13063fabc
-- title:
--   Ab Package: exists is CPMap of iso
-- statement:
--   The Ab Package construction uses the exists is CPMap of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianSchemeCubicalBundleExistsAndMaps.lean#L66-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AbelianSchemeCubicalBundleExistsAndMaps.lean#L66-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_IsCPPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AbelianSchemeCubicalBundleExistsAndMaps
import Theorems.Thm_GlobalTheory_UU_IsWt_mul

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
open GlobalTheory.UU
open GlobalTheory GlobalTheory.AbPackage
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem GlobalTheory.AbPackage.exists_isCPMap_of_iso (hG : GlobalFnsSt) {S' : Scheme.{0}} {f : S' ⟶ S} {B' : Over S'} [GrpObj B']
    [IsCommMonObj B'] (hB' : IsAbelianScheme B') (M : CP B) (M' : CP B') {β : B'.left ⟶ B.left}
    {hw : β ≫ B.hom = B'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hw (x * y) = toBase hw x * toBase hw y)
    (w : LB.Iso M'.L.L (M.L.L.pull β)) (hg : w.IsGen) : ∃ v, IsCPMap M' M f β hw v := by sorry
