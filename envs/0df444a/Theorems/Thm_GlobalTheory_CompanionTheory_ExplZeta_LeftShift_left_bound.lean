-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ExplZeta_LeftShift_left_bound
-- name    : GlobalTheory.CompanionTheory.ExplZeta.LeftShift.left_bound
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:08.750035+00:00
-- url     : https://prove2.me/theorems/eb485d9d-6246-4028-aa43-e1a3f9f51e3d
-- title:
--   Left Shift: left bound
-- statement:
--   The Left Shift construction uses the left bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IntegralLeftVerticalLineBound.lean#L67-L80

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

theorem GlobalTheory.CompanionTheory.ExplZeta.LeftShift.left_bound {g s : ℂ} {A x B : ℝ} (hA : 0 ≤ A) (hx : 2 ≤ x) (hs : s.re ≤ -1)
    (hB : |s.im| ≤ B) (hg : ‖g‖ ≤ A * (1 + |s.re| + |s.im|)) :
    ‖g * (x : ℂ) ^ s / s‖ ≤ A * (1 + |s.re| + B) * Real.exp (s.re / 2) := by sorry
