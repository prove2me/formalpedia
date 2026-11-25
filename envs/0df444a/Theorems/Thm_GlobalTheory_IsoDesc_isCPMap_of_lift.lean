-- Prove2me | Theorems.Thm_GlobalTheory_IsoDesc_isCPMap_of_lift
-- name    : GlobalTheory.IsoDesc.isCPMap_of_lift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:51:36.017018+00:00
-- url     : https://prove2.me/theorems/6b296c32-01f9-5155-897f-cdf4ae5089ab
-- title:
--   Iso Desc: is CPMap of lift
-- statement:
--   The Iso Desc construction uses the is CPMap of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L278-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapDescends.lean#L278-L324

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
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
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B' : Over S'} {B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj B']
  [IsCommMonObj B'] [GrpObj B] [IsCommMonObj B] {P : CP G} {M' : CP B'} {M : CP B} {q : G ⟶ B'}
  {β : B'.left ⟶ B.left} {hβ : β ≫ B.hom = B'.hom ≫ f}

theorem GlobalTheory.IsoDesc.isCPMap_of_lift [IsMonHom q] [Flat q.left] [Surjective q.left]
    (mul : ∀ (T : Over S') (x y : T ⟶ B'), toBase hβ (x * y) = toBase hβ x * toBase hβ y)
    {v : LB.Iso M'.L.L (M.L.L.pull β)} (hv : PGen v)
    (H : ∀ (T : Over S') (z : T.left) (I J), Good M'.L.L z I → Good M.L.L z J →
      Eqns M' M hβ z I J (fun x : T ⟶ G => x ≫ q)
        (fun x => gw v (x ≫ q).left z (J ((x ≫ q).left ≫ β)) (I (x ≫ q).left))) :
    IsCPMap M' M f β hβ v := by sorry
