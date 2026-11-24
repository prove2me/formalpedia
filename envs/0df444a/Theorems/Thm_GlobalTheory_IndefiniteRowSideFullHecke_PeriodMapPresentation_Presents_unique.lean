-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PeriodMapPresentation_Presents_unique
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation.Presents.unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:20.274842+00:00
-- url     : https://prove2.me/theorems/13a8300b-f15a-464c-92fd-57f4ff5c01ac
-- title:
--   Presents: unique
-- statement:
--   The Presents construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PeriodMapPresentation.lean#L70-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PeriodMapPresentation.lean#L70-L84

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation.Presents.unique {D : Datum H} {g : ℕ} {ty ty' : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    {J J' : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La} (h : Presents D ty P J) (h' : Presents D ty' P J') : J = J' := by sorry
