-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_eq_of_injective_baseChange
-- name    : GlobalTheory.ZJ.eq_of_injective_baseChange
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:05.393631+00:00
-- url     : https://prove2.me/theorems/80e1fdf8-d38e-4eb7-b4fd-534fff1860d3
-- title:
--   ZJ: eq of injective base Change
-- statement:
--   The ZJ construction uses the eq of injective base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L14-L23

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

theorem GlobalTheory.ZJ.eq_of_injective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') (h ≫ s) q) (w : a ≫ h = h' ≫ b)
    (hinj : Function.Injective h') {x y : H} (hxy : h x = h y) (hx : s (h x) ∈ Set.range q) : x = y := by sorry
