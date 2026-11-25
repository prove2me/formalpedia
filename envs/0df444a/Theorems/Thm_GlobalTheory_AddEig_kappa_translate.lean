-- Prove2me | Theorems.Thm_GlobalTheory_AddEig_kappa_translate
-- name    : GlobalTheory.AddEig.kappa_translate
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:03:16.530879+00:00
-- url     : https://prove2.me/theorems/2827bbca-3856-594b-9cad-b630e8276772
-- title:
--   Add Eig: kappa translate
-- statement:
--   The Add Eig construction uses the kappa translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionTensorEigenDiagonalThetaOrderTwo.lean#L57-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AdditionTensorEigenDiagonalThetaOrderTwo.lean#L57-L109

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

theorem GlobalTheory.AddEig.kappa_translate (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) {F : Type} [CommRing F]
    (p : Spec (CommRingCat.of F) ⟶ S)
    (κ : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(snd (Over.mk p) (P.A ⊗ P.A) ≫ fst P.A P.A).left, (snd (Over.mk p) (P.A ⊗ P.A) ≫ snd P.A P.A).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * snd P.A P.A)).left,
        (snd (Over.mk p) (P.A ⊗ P.A) ≫ (fst P.A P.A * (snd P.A P.A)⁻¹)).left] ![2, 2, -1, -1])) (hκ : κ.IsGen)
    (c : Over.mk p ⟶ P.A) (hc : c ^ 2 = 1)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk p) P.A).left, (translPt P.A c).left] ![2, -2]))
    (hα : α.IsGen) :
    ∃ r : F, ∀ (T : Over S) (ρ : T ⟶ Over.mk p) (x y : T ⟶ P.A) (z : T.left) (J), Good P.L z J →
      (val α (lift ρ x).left z J * val α (lift ρ y).left z J *
        val κ (lift ρ (lift ((ρ ≫ c) * x) ((ρ ≫ c) * y))).left z J).val =
      gs (𝟙 _) z ⊤ (scal (R := F) ρ.left r) * (val κ (lift ρ (lift x y)).left z J).val := by sorry
