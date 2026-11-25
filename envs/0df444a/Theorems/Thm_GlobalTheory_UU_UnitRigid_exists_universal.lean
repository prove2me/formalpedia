-- Prove2me | Theorems.Thm_GlobalTheory_UU_UnitRigid_exists_universal
-- name    : GlobalTheory.UU.UnitRigid.exists_universal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:32:36.457464+00:00
-- url     : https://prove2.me/theorems/fab50441-5923-47e0-8a69-e2216e4f54cd
-- title:
--   Unit Rigid: exists universal
-- statement:
--   The Unit Rigid construction uses the exists universal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L74-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOneOfGroupLike
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitRigid
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem GlobalTheory.UU.UnitRigid.exists_universal {Y W : Over S} [IsAffine W.left] (y : W ⟶ Y) (u : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ g : AddMonoidAlgebra Γ(W.left, ⊤) X, ∀ (Z : Over S) (s : Z ⟶ W) (t : Z ⟶ splitTorus S X)
      (θ : AddMonoidAlgebra Γ(W.left, ⊤) X →+* Γ(Z.left, ⊤)),
      (∀ b, θ (AddMonoidAlgebra.single 0 b) = s.left.appTop.hom b) →
      (∀ χ, θ (AddMonoidAlgebra.single χ 1) = (chV t χ).val) → (lift t (s ≫ y)).left.appTop.hom u = θ g := by sorry
