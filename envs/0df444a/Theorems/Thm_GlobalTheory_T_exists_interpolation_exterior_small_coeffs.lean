-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_interpolation_exterior_small_coeffs
-- name    : GlobalTheory.T.exists_interpolation_exterior_small_coeffs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:37:13.469568+00:00
-- url     : https://prove2.me/theorems/265d442d-3009-482b-8044-b84c1f7b4f36
-- title:
--   T: exists interpolation exterior small coeffs
-- statement:
--   The T construction uses the exists interpolation exterior small coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_interpolation_exterior_small_coeffs : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by sorry
