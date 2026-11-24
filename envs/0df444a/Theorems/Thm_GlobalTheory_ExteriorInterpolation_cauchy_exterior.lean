-- Prove2me | Theorems.Thm_GlobalTheory_ExteriorInterpolation_cauchy_exterior
-- name    : GlobalTheory.ExteriorInterpolation.cauchy_exterior
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:33.971446+00:00
-- url     : https://prove2.me/theorems/88b74cc0-9064-4ee9-9ee9-70d1170333dc
-- title:
--   Exterior Interpolation: cauchy exterior
-- statement:
--   The Exterior Interpolation construction uses the cauchy exterior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L91-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L91-L216

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

theorem GlobalTheory.ExteriorInterpolation.cauchy_exterior (g : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hg : DifferentiableOn ℂ g {w | r ≤ ‖w‖}) (h0 : Tendsto g (Filter.cocompact ℂ) (𝓝 0))
    (w : ℂ) (hw : r < ‖w‖) :
    ∮ ζ in C(0, r), (ζ - w)⁻¹ * g ζ = -(2 * Real.pi * I * g w) := by sorry
