-- Prove2me | Theorems.Thm_GlobalTheory_UU_torus_stable_of_red
-- name    : GlobalTheory.UU.torus_stable_of_red
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:11:44.601471+00:00
-- url     : https://prove2.me/theorems/ba235a92-e578-53a3-a0a2-44285130e8fa
-- title:
--   UU: torus stable of red
-- statement:
--   The UU construction uses the torus stable of red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableOfSurjective.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableOfSurjective.lean#L60-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
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
noncomputable section
open GlobalTheory GlobalTheory.UU

theorem GlobalTheory.UU.torus_stable_of_red : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (i₀ : splitTorus _ X ⟶ G₀) (i : splitTorus _ X ⟶ G), TorusCompat (red J) F i₀ i → ∀ W : G.left.Opens, (snd (splitTorus _ X) G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) ≤ ((fst (splitTorus _ X) G₀ ≫ i₀) * snd _ G₀).left ⁻¹ᵁ (F ⁻¹ᵁ W) → (snd (splitTorus _ X) G).left ⁻¹ᵁ W ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ W := by sorry
