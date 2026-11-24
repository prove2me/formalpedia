-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_horiz_integral
-- name    : GlobalTheory.CompanionTheory.ExplZeta.LeftShift.horiz_integral
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:50.204196+00:00
-- url     : https://prove2.me/theorems/e01b6fa4-5753-4e92-b8c2-4a262e8f3258
-- title:
--   Left Shift: horiz integral
-- statement:
--   The Left Shift construction uses the horiz integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L94-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L94-L107

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift

theorem GlobalTheory.CompanionTheory.ExplZeta.LeftShift.horiz_integral {f : ℝ → ℂ} {A R : ℝ} (hA : 0 ≤ A) (hR : 1 ≤ R)
    (h : ∀ σ : ℝ, -R ≤ σ → σ ≤ -(1 / 2) → ‖f σ‖ ≤ 4 * A * Real.exp (σ / 4)) :
    ‖∫ σ : ℝ in (-R)..(-(1 / 2)), f σ‖ ≤ 16 * A := by sorry
