-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_surjective_of_isClosedImmersion_of_points
-- name    : GlobalTheory.ZJ.surjective_of_isClosedImmersion_of_points
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:02:40.955948+00:00
-- url     : https://prove2.me/theorems/9c2ca024-15d8-4734-99bc-005da28e7c30
-- title:
--   ZJ: surjective of is Closed Immersion of points
-- statement:
--   The ZJ construction uses the surjective of is Closed Immersion of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L34-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ

theorem GlobalTheory.ZJ.surjective_of_isClosedImmersion_of_points {k : Type} [Field k] [IsAlgClosed k] {H X : Scheme.{0}}
    (h : H ⟶ X) [IsClosedImmersion h] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hs : ∀ x : Sp k ⟶ X, x ≫ s = 𝟙 _ → ∃ c : Sp k ⟶ H, c ≫ h = x) : Function.Surjective h := by sorry
