-- Prove2me | Theorems.Thm_GlobalTheory_SecondPosition_compare
-- name    : GlobalTheory.SecondPosition.compare
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:45:13.185812+00:00
-- url     : https://prove2.me/theorems/c68a77aa-64c5-5ceb-b1be-bb165f6d4a47
-- title:
--   Second Position: compare
-- statement:
--   The Second Position construction uses the compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiMulPsiOfAdditionSecondVariable.lean#L51-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiMulPsiOfAdditionSecondVariable.lean#L51-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalNeZeroOfIsIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIntegralTensorLeftOfSmoothGrpObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionFirstVariable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiMulPsiOfAdditionSecondVariable
import Theorems.Thm_GlobalTheory_FirstSlot_compare

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
open GlobalTheory
open GlobalTheory.SecondPosition
open FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.SecondPosition.compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (y : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : sval (s₀ 0) (lift ρ (y * cT D T mu)).left z J ≠ 0)
    (h0' : sval (s₀ 0) (lift ρ (y⁻¹ * cT D T (-mu))).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s' i (0 + 2 • mu)) (lift ρ y).left z J =
      C * (sval (s' i 0) (lift ρ (y * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (-mu)) y y⁻¹).val *
        ((val (D.psi mu) κ.left z J).val * (val (D.psi (-mu)) κ.left z J).val *
          (val D.sym (y * cT D T mu).left z J).val) =
      C * (U * (val (D.psi 0) κ.left z J).val * (val (D.psi 0) κ.left z J).val) *
        ((cubV D.cub z J (cT D T (mu - -mu)) (cT D T (-mu)) y).val * (val D.sym y.left z J).val) := by sorry
