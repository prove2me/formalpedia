-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_IsPsiCoord_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord.unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:22.441051+00:00
-- url     : https://prove2.me/theorems/01c8d04c-e9aa-4ab7-9991-40f622ce81ba
-- title:
--   Is Psi Coord: unique
-- statement:
--   The Is Psi Coord construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L65-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/GeneratorValues.lean#L65-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsPsiCoord.unique {D : DegPre R} {χ : D.X} {x x' : (FractionRing R)ˣ}
    (hx : IsPsiCoord D χ x) (hx' : IsPsiCoord D χ x') :
    ∃ u : Rˣ, x = Units.map (algebraMap R (FractionRing R)).toMonoidHom u * x' := by sorry
