-- Prove2me | Theorems.Thm_GlobalTheory_T_iteratedDeriv_eq_of_eq_on_real_segment
-- name    : GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:29.073565+00:00
-- url     : https://prove2.me/theorems/5c910283-22a8-41cc-9270-ca76bf8ad892
-- title:
--   T: iterated Deriv eq of eq on real segment
-- statement:
--   The T construction uses the iterated Deriv eq of eq on real segment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivEqOfEqOnRealSegmentStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IteratedDerivEqOfEqOnRealSegmentStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivEqOfEqOnRealSegment
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivEqOfEqOnRealSegmentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.iteratedDeriv_eq_of_eq_on_real_segment : ∀ (f g : ℂ → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ f (Metric.ball 0 ρ) → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ s : ℝ, |s| < ρ → f s = g s) → ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0 := by sorry
