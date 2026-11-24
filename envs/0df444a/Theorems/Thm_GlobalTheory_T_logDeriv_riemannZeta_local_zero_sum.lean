-- Prove2me | Theorems.Thm_GlobalTheory_T_logDeriv_riemannZeta_local_zero_sum
-- name    : GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:51.931911+00:00
-- url     : https://prove2.me/theorems/bc5cd80a-1216-49dd-86de-f3d31a24ddb5
-- title:
--   T: log Deriv riemann Zeta local zero sum
-- statement:
--   The T construction uses the log Deriv riemann Zeta local zero sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSumStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivRiemannZetaLocalZeroSumStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by sorry
