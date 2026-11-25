-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_isCompleteLocalNormal_padicInt
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.isCompleteLocalNormal_padicInt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:40.212997+00:00
-- url     : https://prove2.me/theorems/0e3bf315-ca48-4e4a-acb9-ceb1a68217c5
-- title:
--   Complete Local Normal Rings: is Complete Local Normal padic Int
-- statement:
--   The Complete Local Normal Rings construction uses the is Complete Local Normal padic Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L29-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RawDegreeForms
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.isCompleteLocalNormal_padicInt (p : ℕ) [Fact p.Prime] : IsCompleteLocalNormal ℤ_[p] := by sorry
