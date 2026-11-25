-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_isAdicNormalPair_powerSeries
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.isAdicNormalPair_powerSeries
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:32.0896+00:00
-- url     : https://prove2.me/theorems/a6830ae6-fdb1-4387-bd48-a9a3a1376384
-- title:
--   Complete Local Normal Rings: is Adic Normal Pair power Series
-- statement:
--   The Complete Local Normal Rings construction uses the is Adic Normal Pair power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L32-L35

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.isAdicNormalPair_powerSeries (O : Type) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] :
    IsAdicNormalPair (PowerSeries O) (Ideal.span {PowerSeries.X}) := by sorry
