-- Prove2me | Theorems.Thm_GlobalTheory_hom_ext_of_geometricPoints_dense
-- name    : GlobalTheory.hom_ext_of_geometricPoints_dense
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:10.73586+00:00
-- url     : https://prove2.me/theorems/1f37d849-65a2-4e0b-be81-cab79746c1cd
-- title:
--   Global Theory: hom ext of geometric Points dense
-- statement:
--   The Global Theory construction uses the hom ext of geometric Points dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftClosedImmersionOfDense.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLiftClosedImmersionOfDense.lean#L10-L24

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

theorem GlobalTheory.hom_ext_of_geometricPoints_dense {X Y S : Scheme.{0}} [IsReduced X] (t : Y ⟶ S)
    [IsSeparated t] (f g : X ⟶ Y) (h : f ≫ t = g ≫ t) (D : Set X) (hD : Dense D)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.range x ⊆ D →
      x ≫ f = x ≫ g) : f = g := by sorry
