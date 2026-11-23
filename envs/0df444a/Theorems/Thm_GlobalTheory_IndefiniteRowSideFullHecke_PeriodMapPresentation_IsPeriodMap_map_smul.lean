-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PeriodMapPresentation_IsPeriodMap_map_smul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation.IsPeriodMap.map_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:05.434665+00:00
-- url     : https://prove2.me/theorems/0ef51eb7-74f4-41d0-a734-05f385469570
-- title:
--   Is Period Map: map smul
-- statement:
--   The Is Period Map construction uses the map smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PeriodMapPresentation.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PeriodMapPresentation.lean#L64-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation.IsPeriodMap.map_smul {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (h : IsPeriodMap D ty P) (a : 𝓞 E) (x : D.La) : P (a • x) = tyAct ty a (P x) := by sorry
