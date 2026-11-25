-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CompleteLocalNormalRings_IsCompleteLocalNormal_pair
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.IsCompleteLocalNormal.pair
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:49.85049+00:00
-- url     : https://prove2.me/theorems/95912784-c31b-4daf-a58f-bc4d93ab40d8
-- title:
--   Is Complete Local Normal: pair
-- statement:
--   The Is Complete Local Normal construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/RawDegreeForms.lean#L25-L27

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.CompleteLocalNormalRings.IsCompleteLocalNormal.pair {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (h : IsCompleteLocalNormal R) : IsAdicNormalPair R (IsLocalRing.maximalIdeal R) := by sorry
