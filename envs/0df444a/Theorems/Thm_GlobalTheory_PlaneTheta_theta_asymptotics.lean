-- Prove2me | Theorems.Thm_GlobalTheory_PlaneTheta_theta_asymptotics
-- name    : GlobalTheory.PlaneTheta.theta_asymptotics
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:48:46.478353+00:00
-- url     : https://prove2.me/theorems/c435e837-85bc-40b7-9c3c-b8162557a28d
-- title:
--   Plane Theta: theta asymptotics
-- statement:
--   The Plane Theta construction uses the theta asymptotics property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L133-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeThetaAsymptotics.lean#L133-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta

theorem GlobalTheory.PlaneTheta.theta_asymptotics : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by sorry
