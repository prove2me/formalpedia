-- Prove2me | Theorems.Thm_GlobalTheory_ExteriorInterpolation_exists_coeffs
-- name    : GlobalTheory.ExteriorInterpolation.exists_coeffs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:52.011876+00:00
-- url     : https://prove2.me/theorems/0aef40e9-223e-4619-abdc-a3af5046600c
-- title:
--   Exterior Interpolation: exists coeffs
-- statement:
--   The Exterior Interpolation construction uses the exists coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L6-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsInterpolationExteriorSmallCoeffs.lean#L6-L43

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

theorem GlobalTheory.ExteriorInterpolation.exists_coeffs (l : ℕ) (z : Fin l → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ a : ℕ → ℂ, (∀ w : ℂ, ∏ i, (w - z i) = ∑ k ∈ Finset.range (l + 1), a k * w ^ k) ∧
      ∑ k ∈ Finset.range (l + 1), ‖a k‖ ≤ 2 ^ l := by sorry
