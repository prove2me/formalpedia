-- Prove2me | Theorems.Thm_GlobalTheory_SquareZero_mul_eq_zero_of_app_eq_zero
-- name    : GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:34:27.876855+00:00
-- url     : https://prove2.me/theorems/68f2e1d1-6126-5e69-b8e6-ee0d23d0bb59
-- title:
--   Square Zero: mul eq zero of app eq zero
-- statement:
--   The Square Zero construction uses the mul eq zero of app eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulEqZeroOfAppEqZero.lean#L23-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MulEqZeroOfAppEqZero.lean#L23-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSectionEqMulOfVanishingModElement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulEqZeroOfAppEqZero
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
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace
open GlobalTheory GlobalTheory.SquareZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X X' : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X),
    IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : X.Opens) (x y : Γ(X, W)),
    (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0 := by sorry
