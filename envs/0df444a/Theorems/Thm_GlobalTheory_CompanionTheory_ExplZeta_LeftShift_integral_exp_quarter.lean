-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_integral_exp_quarter
-- name    : GlobalTheory.CompanionTheory.ExplZeta.LeftShift.integral_exp_quarter
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:38.984022+00:00
-- url     : https://prove2.me/theorems/3cdf7713-2b91-470e-bb8a-e254c3d1694c
-- title:
--   Left Shift: integral exp quarter
-- statement:
--   The Left Shift construction uses the integral exp quarter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L82-L92

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

theorem GlobalTheory.CompanionTheory.ExplZeta.LeftShift.integral_exp_quarter {R : ℝ} :
    ∫ σ : ℝ in (-R)..(-(1 / 2)), Real.exp (σ / 4)
      = 4 * (Real.exp (-(1 / 2) / 4) - Real.exp (-R / 4)) := by sorry
