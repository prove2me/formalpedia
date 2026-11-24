-- Prove2me | Theorems.Thm_GlobalTheory_exists_local_unit_of_weight
-- name    : GlobalTheory.exists_local_unit_of_weight
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:40.444368+00:00
-- url     : https://prove2.me/theorems/3339578c-2f19-46b0-bd9d-371170f0a598
-- title:
--   Global Theory: exists local unit of weight
-- statement:
--   The Global Theory construction uses the exists local unit of weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L382-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L382-L421

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open TorsorUnit SplitTorusPoints

theorem GlobalTheory.exists_local_unit_of_weight :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → IsAffineHom q.left → ∀ (χ : X) (b : B.left), ∃ (V : B.left.Opens) (_ : b ∈ V) (u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u.val = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u.val := by sorry
