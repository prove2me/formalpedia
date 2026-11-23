-- Prove2me | Theorems.Thm_GlobalTheory_dbar_mul
-- name    : GlobalTheory.dbar_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:07.434916+00:00
-- url     : https://prove2.me/theorems/e713bfe4-244d-4044-a5b7-4646f30a1287
-- title:
--   Global Theory: dbar mul
-- statement:
--   The Global Theory construction uses the dbar mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L227-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/EventuallyDifferentiableAtOfContDiffAtTwo.lean#L227-L228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {f g : E → F} {z : E}

theorem GlobalTheory.dbar_mul {a b : E → ℂ} (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) (v : E) :
    dbar (fun x => a x * b x) z v = a z * dbar b z v + dbar a z v * b z := by sorry
