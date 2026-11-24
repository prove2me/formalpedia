-- Prove2me | Theorems.Thm_GlobalTheory_T_differentiableAt_coordinate_cauchy_integral
-- name    : GlobalTheory.T.differentiableAt_coordinate_cauchy_integral
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:36.600225+00:00
-- url     : https://prove2.me/theorems/bb9be2b2-6f25-4fc1-84cf-c703418a6080
-- title:
--   T: differentiable At coordinate cauchy integral
-- statement:
--   The T construction uses the differentiable At coordinate cauchy integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtCoordinateCauchyIntegralStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DifferentiableAtCoordinateCauchyIntegralStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtCoordinateCauchyIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtCoordinateCauchyIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.differentiableAt_coordinate_cauchy_integral : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by sorry
