-- Prove2me | Theorems.Thm_GlobalTheory_cauchyCoord_differentiableAt
-- name    : GlobalTheory.cauchyCoord_differentiableAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:00.910946+00:00
-- url     : https://prove2.me/theorems/f287106a-21da-4384-8d73-5651865b77dc
-- title:
--   Global Theory: cauchy Coord differentiable At
-- statement:
--   The Global Theory construction uses the cauchy Coord differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtCoordinateCauchyIntegral.lean#L21-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtCoordinateCauchyIntegral.lean#L21-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtCoordinateCauchyIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
noncomputable section
open GlobalTheory

theorem GlobalTheory.cauchyCoord_differentiableAt :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ),
      0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U →
      DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} →
      DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by sorry
