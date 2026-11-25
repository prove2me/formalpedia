-- Prove2me | Theorems.Thm_GlobalTheory_T_torusStable_affineOpen_functions_weightGraded
-- name    : GlobalTheory.T.torusStable_affineOpen_functions_weightGraded
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:25.293876+00:00
-- url     : https://prove2.me/theorems/2f0a920f-83c1-4649-a3be-16425928034d
-- title:
--   T: torus Stable affine Open functions weight Graded
-- statement:
--   The T construction uses the torus Stable affine Open functions weight Graded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGradedStatement.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TorusStableAffineOpenFunctionsWeightGradedStatement.lean#L14-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
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

theorem GlobalTheory.T.torusStable_affineOpen_functions_weightGraded : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V → (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧ ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0) := by sorry
