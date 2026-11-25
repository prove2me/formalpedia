-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitSphereMeasure_eval_hermitianLinearForm
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.eval_hermitianLinearForm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:37.531939+00:00
-- url     : https://prove2.me/theorems/7e6eb7d7-1116-4436-a2eb-eab5c0315e2d
-- title:
--   Unit Sphere Measure: eval hermitian Linear Form
-- statement:
--   The Unit Sphere Measure construction uses the eval hermitian Linear Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L211-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SphereBlockLogMean.lean#L211-L213

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.eval_hermitianLinearForm {N : ℕ} (u z : EuclideanSpace ℂ (Fin (N + 1))) :
    eval (fun j => z j) (hermitianLinearForm u) = inner ℂ u z := by sorry
