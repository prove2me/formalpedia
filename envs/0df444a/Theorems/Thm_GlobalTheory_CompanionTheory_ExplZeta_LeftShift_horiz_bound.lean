-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_horiz_bound
-- name    : GlobalTheory.CompanionTheory.ExplZeta.LeftShift.horiz_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:57.198255+00:00
-- url     : https://prove2.me/theorems/4ab59404-5d7f-40f8-aa5e-4db5ccd9287d
-- title:
--   Left Shift: horiz bound
-- statement:
--   The Left Shift construction uses the horiz bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L42-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L42-L65

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

theorem GlobalTheory.CompanionTheory.ExplZeta.LeftShift.horiz_bound {g s : ℂ} {A x : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ 0)
    (him : 1 ≤ |s.im|) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ 4 * A * Real.exp (s.re / 4) := by sorry
