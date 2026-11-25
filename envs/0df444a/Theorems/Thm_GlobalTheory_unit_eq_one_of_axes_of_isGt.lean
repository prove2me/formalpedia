-- Prove2me | Theorems.Thm_GlobalTheory_unit_eq_one_of_axes_of_isGt
-- name    : GlobalTheory.unit_eq_one_of_axes_of_isGt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:26:07.524015+00:00
-- url     : https://prove2.me/theorems/c2528809-e5b4-5bbb-b19f-347605924049
-- title:
--   Global Theory: unit eq one of axes of is Gt
-- statement:
--   The Global Theory construction uses the unit eq one of axes of is Gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L318-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L318-L329

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open UnitRigidity

theorem GlobalTheory.unit_eq_one_of_axes_of_isGt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ u : Γ((G ⊗ G).left, ⊤), IsUnit u → (lift (𝟙 G) (1 : G ⟶ G)).left.appTop.hom u = 1 → (lift (1 : G ⟶ G) (𝟙 G)).left.appTop.hom u = 1 → u = 1 := by sorry
