-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitSphereMeasure_heightZeroOnFractions_of_additive
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.heightZeroOnFractions_of_additive
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:25.024686+00:00
-- url     : https://prove2.me/theorems/9920ac0a-dde5-5947-99ee-7cd3333102d2
-- title:
--   Unit Sphere Measure: height Zero On Fractions of additive
-- statement:
--   The Unit Sphere Measure construction uses the height Zero On Fractions of additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L204-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L204-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.heightZeroOnFractions_of_additive (h : HeightZeroAdditive) : HeightZeroOnFractions := by sorry
