-- Prove2me | Theorems.Thm_GlobalTheory_UU_UnitRigid_eq_one_affine
-- name    : GlobalTheory.UU.UnitRigid.eq_one_affine
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:14.427244+00:00
-- url     : https://prove2.me/theorems/d47630e3-7439-43f2-b36f-38f64e0d71c9
-- title:
--   Unit Rigid: eq one affine
-- statement:
--   The Unit Rigid construction uses the eq one affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L89-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EqOneOfGroupLike.lean#L89-L139

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

theorem GlobalTheory.UU.UnitRigid.eq_one_affine {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) {Y W : Over (Spec (CommRingCat.of A))}
    [IsAffine W.left] (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤))
    (hm : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u = (lift t y).left.appTop.hom u * (lift t' y).left.appTop.hom u)
    (h₁ : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift t y).left.appTop.hom u = 1) (t : W ⟶ splitTorus _ X) (y : W ⟶ Y) : (lift t y).left.appTop.hom u = 1 := by sorry
