-- Prove2me | Theorems.Thm_GlobalTheory_FirstSlot_compare
-- name    : GlobalTheory.FirstSlot.compare
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:11.751946+00:00
-- url     : https://prove2.me/theorems/3e892f35-359d-4326-866b-4ed3ee760746
-- title:
--   First Slot: compare
-- statement:
--   The First Slot construction uses the compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiMulPsiOfAdditionFirstVariable.lean#L40-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PsiMulPsiOfAdditionFirstVariable.lean#L40-L69

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
open GlobalTheory.FirstSlot
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.FirstSlot.compare (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (s₀ : ∀ α, SecBT D T₀ 1 α) (r : R) {n : ℕ}
    (s s' : Fin n → ∀ α, SecBT D T₀ 2 α) (hA : AddB D T₀ s₀ r s s') (hP : PsiRel D T₀ s₀) (a b mu : D.X)
    (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ T₀) (κ : T ⟶ TK R) (x : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) [IsDomain (T.left.presheaf.stalk z)] (hr : gs (𝟙 _) z ⊤ (scal T.hom r) ≠ 0)
    (h0 : ∀ χ, sval (s₀ 0) (lift ρ (x * cT D T χ)).left z J ≠ 0) (C U : T.left.presheaf.stalk z)
    (hs : ∀ i, sval (s i (a + b + 2 • mu)) (lift ρ x).left z J =
      C * (sval (s i (a + b)) (lift ρ (x * cT D T mu)).left z J * U)) :
    (cubV D.cub z J (cT D T (a + mu)) (cT D T (b + mu)) x).val *
        ((val (D.psi (a + mu)) κ.left z J).val * (val (D.psi (b + mu)) κ.left z J).val) =
      C * (U * (cubV D.cub z J (cT D T a) (cT D T b) (x * cT D T mu)).val * (val (D.psi a) κ.left z J).val *
        (val (D.psi b) κ.left z J).val) := by sorry
