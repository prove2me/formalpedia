-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_rpow_le_exp_half
-- name    : GlobalTheory.CompanionTheory.ExplZeta.LeftShift.rpow_le_exp_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:10.667033+00:00
-- url     : https://prove2.me/theorems/a1dded45-e60c-4b22-a3fb-26b3d7ca00a0
-- title:
--   Left Shift: rpow le exp half
-- statement:
--   The Left Shift construction uses the rpow le exp half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L6-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L6-L15

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

theorem GlobalTheory.CompanionTheory.ExplZeta.LeftShift.rpow_le_exp_half {x σ : ℝ} (hx : 2 ≤ x) (hσ : σ ≤ 0) :
    x ^ σ ≤ Real.exp (σ / 2) := by sorry
