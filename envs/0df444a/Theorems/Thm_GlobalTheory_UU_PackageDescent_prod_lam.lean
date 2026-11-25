-- Prove2me | Theorems.Thm_GlobalTheory_UU_PackageDescent_prod_lam
-- name    : GlobalTheory.UU.PackageDescent.prod_lam
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:02:34.354748+00:00
-- url     : https://prove2.me/theorems/1be8c22c-b20e-5c0a-bb75-ce18af7be39d
-- title:
--   Package Descent: prod lam
-- statement:
--   The Package Descent construction uses the prod lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L161-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L161-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {i : H ⟶ G}
omit [GrpObj H]

theorem GlobalTheory.UU.PackageDescent.prod_lam {T : Over S} (t : T ⟶ H) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k : Fin 4, h ((lift t x).left ≫ lamφ i k) ^ Oε k =
      h ((t ≫ i) * x).left * (h (t ≫ i).left)⁻¹ * (h x.left)⁻¹ * h (1 : T ⟶ G).left := by sorry
