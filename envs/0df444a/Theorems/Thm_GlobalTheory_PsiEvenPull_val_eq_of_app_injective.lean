-- Prove2me | Theorems.Thm_GlobalTheory_PsiEvenPull_val_eq_of_app_injective
-- name    : GlobalTheory.PsiEvenPull.val_eq_of_app_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:08.036934+00:00
-- url     : https://prove2.me/theorems/0191fa75-1a66-4ff1-8f67-4ed353231b84
-- title:
--   Psi Even Pull: val eq of app injective
-- statement:
--   The Psi Even Pull construction uses the val eq of app injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValEqOfAppInjective.lean#L16-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PsiEvenPull

theorem GlobalTheory.PsiEvenPull.val_eq_of_app_injective {X Y Y' : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ' ε' φ ε)
    (κ : Y' ⟶ Y) (hκ : ∀ U : Y.Opens, Function.Injective (κ.app U).hom)
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u κ y J = val u' κ y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J)
    (hJ : Good M z J) : val u r z J = val u' r z J := by sorry
