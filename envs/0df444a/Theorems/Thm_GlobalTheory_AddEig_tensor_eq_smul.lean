-- Prove2me | Theorems.Thm_GlobalTheory_AddEig_tensor_eq_smul
-- name    : GlobalTheory.AddEig.tensor_eq_smul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:52:27.79565+00:00
-- url     : https://prove2.me/theorems/cc97d969-c889-552f-bc4d-fbf16159cf13
-- title:
--   Add Eig: tensor eq smul
-- statement:
--   The Add Eig construction uses the tensor eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionTensorEigenDiagonalThetaOrderTwo.lean#L111-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionTensorEigenDiagonalThetaOrderTwo.lean#L111-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalOfIsTwistPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSumTmulLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdditionTensorEigenDiagonalThetaOrderTwo
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
open GlobalTheory GlobalTheory.AddEig

theorem GlobalTheory.AddEig.tensor_eq_smul {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (q : Y ⟶ Spec (CommRingCat.of F)) [QuasiCompact q] [IsSeparated q] {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} (u u' t t' : Fin n → SecMod q (LB.LinComb L φ ε)) (r : F)
    (H : ∀ (Z : Scheme.{0}) (r₁ r₂ : Z ⟶ Y), r₁ ≫ q = r₂ ≫ q → ∀ (z : Z) (J), Good L z J →
      ∑ i, sval (u i).sec r₁ z J * sval (u' i).sec r₂ z J =
        gs (𝟙 _) z ⊤ (scal (r₁ ≫ q) r) * ∑ i, sval (t i).sec r₁ z J * sval (t' i).sec r₂ z J) :
    ∑ i, TensorProduct.tmul F (u i) (u' i) = r • ∑ i, TensorProduct.tmul F (t i) (t' i) := by sorry
