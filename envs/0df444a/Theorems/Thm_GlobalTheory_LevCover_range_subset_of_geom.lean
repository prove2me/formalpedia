-- Prove2me | Theorems.Thm_GlobalTheory_LevCover_range_subset_of_geom
-- name    : GlobalTheory.LevCover.range_subset_of_geom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:06.405826+00:00
-- url     : https://prove2.me/theorems/79f0b16a-08fc-4816-a72d-66143c67872d
-- title:
--   Lev Cover: range subset of geom
-- statement:
--   The Lev Cover construction uses the range subset of geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L135-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L135-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {S : Scheme.{0}}

theorem GlobalTheory.LevCover.range_subset_of_geom {T Z : Over S} (h : T ⟶ Z) (U : Set Z.left)
    (H : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ T), Set.range (y ≫ h).left ⊆ U) :
    Set.range h.left ⊆ U := by sorry
