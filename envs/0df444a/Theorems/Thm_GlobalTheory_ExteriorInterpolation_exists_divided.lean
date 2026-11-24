-- Prove2me | Theorems.Thm_GlobalTheory_ExteriorInterpolation_exists_divided
-- name    : GlobalTheory.ExteriorInterpolation.exists_divided
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:40.219251+00:00
-- url     : https://prove2.me/theorems/6cd2709a-ff7f-4722-a9ad-5a09fe9e1698
-- title:
--   Exterior Interpolation: exists divided
-- statement:
--   The Exterior Interpolation construction uses the exists divided property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L45-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L45-L89

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

theorem GlobalTheory.ExteriorInterpolation.exists_divided (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ b : Fin l → ℂ → ℂ, (∀ j, Continuous (b j)) ∧ (∀ j ζ, ‖ζ‖ ≤ 1 → ‖b j ζ‖ ≤ 2 ^ l) ∧
      ∀ ζ w : ℂ, (∑ j, b j ζ * w ^ (j : ℕ)) * (ζ - w) = ∏ i, (ζ - z i) - ∏ i, (w - z i) := by sorry
