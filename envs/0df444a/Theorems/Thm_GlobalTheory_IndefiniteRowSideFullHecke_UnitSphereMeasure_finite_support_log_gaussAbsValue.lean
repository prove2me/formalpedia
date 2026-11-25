-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitSphereMeasure_finite_support_log_gaussAbsValue
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.finite_support_log_gaussAbsValue
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:36.376665+00:00
-- url     : https://prove2.me/theorems/879f4561-5852-4b9f-8784-9c22210081f4
-- title:
--   Unit Sphere Measure: finite support log gauss Abs Value
-- statement:
--   The Unit Sphere Measure construction uses the finite support log gauss Abs Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L127-L136

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.finite_support_log_gaussAbsValue {ι : Type} {ω : MvPolynomial ι K} (h : ω ≠ 0) :
    (Function.support fun w : FinitePlace K => Real.log (gaussAbsValue w ω)).Finite := by sorry
