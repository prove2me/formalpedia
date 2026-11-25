-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitSphereMeasure_finitePlace_eq_absNorm_zpow
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.finitePlace_eq_absNorm_zpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:43.355457+00:00
-- url     : https://prove2.me/theorems/b88582f4-4615-48b6-bc6f-a4f0602f62be
-- title:
--   Unit Sphere Measure: finite Place eq abs Norm zpow
-- statement:
--   The Unit Sphere Measure construction uses the finite Place eq abs Norm zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L96-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L96-L105

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
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.finitePlace_eq_absNorm_zpow (w : FinitePlace K) {c : K} (hc : c ≠ 0) :
    w c = (Ideal.absNorm w.maximalIdeal.asIdeal : ℝ) ^
      (WithZero.log (w.maximalIdeal.valuation K c)) := by sorry
