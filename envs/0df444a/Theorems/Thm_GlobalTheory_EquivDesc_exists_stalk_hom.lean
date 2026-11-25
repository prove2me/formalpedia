-- Prove2me | Theorems.Thm_GlobalTheory_EquivDesc_exists_stalk_hom
-- name    : GlobalTheory.EquivDesc.exists_stalk_hom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:36:31.13671+00:00
-- url     : https://prove2.me/theorems/0042af34-2c8e-4b4b-948b-3360f2f22435
-- title:
--   Equiv Desc: exists stalk hom
-- statement:
--   The Equiv Desc construction uses the exists stalk hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L22-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L22-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
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
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}

theorem GlobalTheory.EquivDesc.exists_stalk_hom {Z Z' : Scheme.{0}} (κ : Z' ⟶ Z) [IsOpenImmersion κ] (z : Z') :
    ∃ Φ : (Z.presheaf.stalk (κ z))ˣ →* (Z'.presheaf.stalk z)ˣ, Function.Injective Φ ∧
      ∀ (Y : Scheme.{0}) (f : Z ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)ˣ), f (κ z) ∈ U →
        Φ (gm f (κ z) U a) = gm (κ ≫ f) z U a := by sorry
