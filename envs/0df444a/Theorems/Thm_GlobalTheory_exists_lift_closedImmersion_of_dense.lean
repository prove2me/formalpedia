-- Prove2me | Theorems.Thm_GlobalTheory_exists_lift_closedImmersion_of_dense
-- name    : GlobalTheory.exists_lift_closedImmersion_of_dense
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:52.321546+00:00
-- url     : https://prove2.me/theorems/e137419b-a2d3-45fb-a378-925f845335b6
-- title:
--   Global Theory: exists lift closed Immersion of dense
-- statement:
--   The Global Theory construction uses the exists lift closed Immersion of dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftClosedImmersionOfDense.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftClosedImmersionOfDense.lean#L26-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
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
open GlobalTheory

theorem GlobalTheory.exists_lift_closedImmersion_of_dense {X Y Z : Scheme.{0}} [IsReduced X] (i : Z ⟶ Y)
    [IsClosedImmersion i] (f : X ⟶ Y) (D : Set X) (hD : Dense D)
    (H : ∀ x ∈ D, f x ∈ Set.range i) : ∃ f' : X ⟶ Z, f' ≫ i = f := by sorry
