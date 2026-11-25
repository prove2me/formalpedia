-- Prove2me | Theorems.Thm_GlobalTheory_TorusGrading_exists_expansion
-- name    : GlobalTheory.TorusGrading.exists_expansion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:05:22.477781+00:00
-- url     : https://prove2.me/theorems/2edd474f-1ca0-58fc-9271-eaa74b7e2465
-- title:
--   Torus Grading: exists expansion
-- statement:
--   The Torus Grading construction uses the exists expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L69-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGraded.lean#L69-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
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
open GlobalTheory
open GlobalTheory.TorusGrading
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {V : G.left.Opens}

theorem GlobalTheory.TorusGrading.exists_expansion (hV : IsAffineOpen V)
    (hst : (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V)
    (u : Γ(G.left, V)) : ∃ a : X →₀ Γ(G.left, V), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
      (((t ≫ i) * g).left.appLE V ⊤ h₁).hom u =
        ∑ χ ∈ a.support, (chV t χ).val * (g.left.appLE V ⊤ h₂).hom (a χ) := by sorry
