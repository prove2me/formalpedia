-- Prove2me | Theorems.Thm_GlobalTheory_LevCover_RepTors_ext
-- name    : GlobalTheory.LevCover.RepTors.ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:27.75455+00:00
-- url     : https://prove2.me/theorems/9c3157aa-27bc-418d-9ce5-56d3f9fcc61b
-- title:
--   Rep Tors: ext
-- statement:
--   The Rep Tors construction uses the ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RangeSubsetOfGeom.lean#L72-L75

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

theorem GlobalTheory.LevCover.RepTors.ext {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S} {et : La → (Z ⟶ G)}
    (R : RepTors G n La Z et) {T : Over S} {u u' : T ⟶ Z} (h : ∀ a, u ≫ et a = u' ≫ et a) : u = u' := by sorry
