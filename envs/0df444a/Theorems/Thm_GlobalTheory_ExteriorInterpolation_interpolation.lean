-- Prove2me | Theorems.Thm_GlobalTheory_ExteriorInterpolation_interpolation
-- name    : GlobalTheory.ExteriorInterpolation.interpolation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:17:27.45403+00:00
-- url     : https://prove2.me/theorems/1e481f75-1204-4093-9ffb-26be8c640b48
-- title:
--   Exterior Interpolation: interpolation
-- statement:
--   The Exterior Interpolation construction uses the interpolation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L224-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L224-L333

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExteriorInterpolation

theorem GlobalTheory.ExteriorInterpolation.interpolation : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by sorry
